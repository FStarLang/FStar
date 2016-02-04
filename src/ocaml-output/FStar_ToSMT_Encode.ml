
open Prims
let add_fuel = (fun x tl -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
tl
end else begin
(x)::tl
end)

let withenv = (fun c _59_39 -> (match (_59_39) with
| (a, b) -> begin
(a, b, c)
end))

let vargs = (fun args -> (FStar_List.filter (fun _59_1 -> (match (_59_1) with
| (FStar_Util.Inl (_59_43), _59_46) -> begin
false
end
| _59_49 -> begin
true
end)) args))

let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))

let escape_null_name = (fun a -> if (a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = "_") then begin
(Prims.strcat a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText a.FStar_Absyn_Syntax.realname.FStar_Ident.idText)
end else begin
a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end)

let mk_typ_projector_name : FStar_Ident.lident  ->  FStar_Absyn_Syntax.btvdef  ->  Prims.string = (fun lid a -> (let _162_14 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (escape_null_name a))
in (FStar_All.pipe_left escape _162_14)))

let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Absyn_Syntax.bvvdef  ->  Prims.string = (fun lid a -> (let a = (let _162_19 = (FStar_Absyn_Util.unmangle_field_name a.FStar_Absyn_Syntax.ppname)
in {FStar_Absyn_Syntax.ppname = _162_19; FStar_Absyn_Syntax.realname = a.FStar_Absyn_Syntax.realname})
in (let _162_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (escape_null_name a))
in (FStar_All.pipe_left escape _162_20))))

let primitive_projector_by_pos : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (let fail = (fun _59_61 -> (match (()) with
| () -> begin
(let _162_30 = (let _162_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _162_29 lid.FStar_Ident.str))
in (FStar_All.failwith _162_30))
end))
in (let t = (FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _162_31 = (FStar_Absyn_Util.compress_typ t)
in _162_31.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _59_65) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(let b = (FStar_List.nth binders i)
in (match ((Prims.fst b)) with
| FStar_Util.Inl (a) -> begin
(mk_typ_projector_name lid a.FStar_Absyn_Syntax.v)
end
| FStar_Util.Inr (x) -> begin
(mk_term_projector_name lid x.FStar_Absyn_Syntax.v)
end))
end
end
| _59_74 -> begin
(fail ())
end))))

let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _162_37 = (let _162_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _162_36))
in (FStar_All.pipe_left escape _162_37)))

let mk_typ_projector : FStar_Ident.lident  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_ToSMT_Term.term = (fun lid a -> (let _162_43 = (let _162_42 = (mk_typ_projector_name lid a)
in (_162_42, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Type_sort))))
in (FStar_ToSMT_Term.mkFreeV _162_43)))

let mk_term_projector : FStar_Ident.lident  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_ToSMT_Term.term = (fun lid a -> (let _162_49 = (let _162_48 = (mk_term_projector_name lid a)
in (_162_48, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _162_49)))

let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_ToSMT_Term.term = (fun lid i -> (let _162_55 = (let _162_54 = (mk_term_projector_name_by_pos lid i)
in (_162_54, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _162_55)))

let mk_data_tester = (fun env l x -> (FStar_ToSMT_Term.mk_tester (escape l.FStar_Ident.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  FStar_Ident.ident  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_ToSMT_Term.term; next_id : Prims.unit  ->  Prims.int}

let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))

let varops : varops_t = (let initial_ctr = 10
in (let ctr = (FStar_Util.mk_ref initial_ctr)
in (let new_scope = (fun _59_100 -> (match (()) with
| () -> begin
(let _162_159 = (FStar_Util.smap_create 100)
in (let _162_158 = (FStar_Util.smap_create 100)
in (_162_159, _162_158)))
end))
in (let scopes = (let _162_161 = (let _162_160 = (new_scope ())
in (_162_160)::[])
in (FStar_Util.mk_ref _162_161))
in (let mk_unique = (fun y -> (let y = (escape y)
in (let y = (match ((let _162_165 = (FStar_ST.read scopes)
in (FStar_Util.find_map _162_165 (fun _59_108 -> (match (_59_108) with
| (names, _59_107) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_59_111) -> begin
(let _59_113 = (FStar_Util.incr ctr)
in (let _162_167 = (let _162_166 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _162_166))
in (Prims.strcat (Prims.strcat y "__") _162_167)))
end)
in (let top_scope = (let _162_169 = (let _162_168 = (FStar_ST.read scopes)
in (FStar_List.hd _162_168))
in (FStar_All.pipe_left Prims.fst _162_169))
in (let _59_117 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun pp rn -> (let _162_175 = (let _162_174 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _162_174 "__"))
in (Prims.strcat _162_175 rn.FStar_Ident.idText)))
in (let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (let next_id = (fun _59_125 -> (match (()) with
| () -> begin
(let _59_126 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (let fresh = (fun pfx -> (let _162_183 = (let _162_182 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _162_182))
in (FStar_Util.format2 "%s_%s" pfx _162_183)))
in (let string_const = (fun s -> (match ((let _162_187 = (FStar_ST.read scopes)
in (FStar_Util.find_map _162_187 (fun _59_135 -> (match (_59_135) with
| (_59_133, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (let _162_188 = (FStar_ToSMT_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxString _162_188))
in (let top_scope = (let _162_190 = (let _162_189 = (FStar_ST.read scopes)
in (FStar_List.hd _162_189))
in (FStar_All.pipe_left Prims.snd _162_190))
in (let _59_142 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun _59_145 -> (match (()) with
| () -> begin
(let _162_195 = (let _162_194 = (new_scope ())
in (let _162_193 = (FStar_ST.read scopes)
in (_162_194)::_162_193))
in (FStar_ST.op_Colon_Equals scopes _162_195))
end))
in (let pop = (fun _59_147 -> (match (()) with
| () -> begin
(let _162_199 = (let _162_198 = (FStar_ST.read scopes)
in (FStar_List.tl _162_198))
in (FStar_ST.op_Colon_Equals scopes _162_199))
end))
in (let mark = (fun _59_149 -> (match (()) with
| () -> begin
(push ())
end))
in (let reset_mark = (fun _59_151 -> (match (()) with
| () -> begin
(pop ())
end))
in (let commit_mark = (fun _59_153 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(let _59_166 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (let _59_171 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _59_174 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

let unmangle = (fun x -> (let _162_215 = (let _162_214 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.ppname)
in (let _162_213 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.realname)
in (_162_214, _162_213)))
in (FStar_Absyn_Util.mkbvd _162_215)))

type binding =
| Binding_var of (FStar_Absyn_Syntax.bvvdef * FStar_ToSMT_Term.term)
| Binding_tvar of (FStar_Absyn_Syntax.btvdef * FStar_ToSMT_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option)
| Binding_ftvar of (FStar_Ident.lident * Prims.string * FStar_ToSMT_Term.term Prims.option)

let is_Binding_var : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_tvar : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_tvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_fvar : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_fvar (_) -> begin
true
end
| _ -> begin
false
end))

let is_Binding_ftvar : binding  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Binding_ftvar (_) -> begin
true
end
| _ -> begin
false
end))

let ___Binding_var____0 : binding  ->  (FStar_Absyn_Syntax.bvvdef * FStar_ToSMT_Term.term) = (fun projectee -> (match (projectee) with
| Binding_var (_59_179) -> begin
_59_179
end))

let ___Binding_tvar____0 : binding  ->  (FStar_Absyn_Syntax.btvdef * FStar_ToSMT_Term.term) = (fun projectee -> (match (projectee) with
| Binding_tvar (_59_182) -> begin
_59_182
end))

let ___Binding_fvar____0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_59_185) -> begin
_59_185
end))

let ___Binding_ftvar____0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_ToSMT_Term.term Prims.option) = (fun projectee -> (match (projectee) with
| Binding_ftvar (_59_188) -> begin
_59_188
end))

let binder_of_eithervar = (fun v -> (v, None))

type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_Tc_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_ToSMT_Term.sort Prims.list * FStar_ToSMT_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))

let print_env : env_t  ->  Prims.string = (fun e -> (let _162_301 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _59_2 -> (match (_59_2) with
| Binding_var (x, t) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Binding_tvar (a, t) -> begin
(FStar_Absyn_Print.strBvd a)
end
| Binding_fvar (l, s, t, _59_213) -> begin
(FStar_Absyn_Print.sli l)
end
| Binding_ftvar (l, s, t) -> begin
(FStar_Absyn_Print.sli l)
end))))
in (FStar_All.pipe_right _162_301 (FStar_String.concat ", "))))

let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

let caption_t : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string Prims.option = (fun env t -> if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _162_311 = (FStar_Absyn_Print.typ_to_string t)
in Some (_162_311))
end else begin
None
end)

let fresh_fvar : Prims.string  ->  FStar_ToSMT_Term.sort  ->  (Prims.string * FStar_ToSMT_Term.term) = (fun x s -> (let xsym = (varops.fresh x)
in (let _162_316 = (FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _162_316))))

let gen_term_var : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (let ysym = (let _162_321 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _162_321))
in (let y = (FStar_ToSMT_Term.mkFreeV (ysym, FStar_ToSMT_Term.Term_sort))
in (ysym, y, (let _59_232 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _59_232.tcenv; warn = _59_232.warn; cache = _59_232.cache; nolabels = _59_232.nolabels; use_zfuel_name = _59_232.use_zfuel_name; encode_non_total_function_typ = _59_232.encode_non_total_function_typ})))))

let new_term_constant : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (let y = (FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _59_238 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _59_238.depth; tcenv = _59_238.tcenv; warn = _59_238.warn; cache = _59_238.cache; nolabels = _59_238.nolabels; use_zfuel_name = _59_238.use_zfuel_name; encode_non_total_function_typ = _59_238.encode_non_total_function_typ})))))

let push_term_var : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_ToSMT_Term.term  ->  env_t = (fun env x t -> (let _59_243 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _59_243.depth; tcenv = _59_243.tcenv; warn = _59_243.warn; cache = _59_243.cache; nolabels = _59_243.nolabels; use_zfuel_name = _59_243.use_zfuel_name; encode_non_total_function_typ = _59_243.encode_non_total_function_typ}))

let lookup_term_var = (fun env a -> (match ((lookup_binding env (fun _59_3 -> (match (_59_3) with
| Binding_var (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _59_253 -> begin
None
end)))) with
| None -> begin
(let _162_336 = (let _162_335 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound term variable not found: %s" _162_335))
in (FStar_All.failwith _162_336))
end
| Some (b, t) -> begin
t
end))

let gen_typ_var : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (let ysym = (let _162_341 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@a" _162_341))
in (let y = (FStar_ToSMT_Term.mkFreeV (ysym, FStar_ToSMT_Term.Type_sort))
in (ysym, y, (let _59_263 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _59_263.tcenv; warn = _59_263.warn; cache = _59_263.cache; nolabels = _59_263.nolabels; use_zfuel_name = _59_263.use_zfuel_name; encode_non_total_function_typ = _59_263.encode_non_total_function_typ})))))

let new_typ_constant : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (let y = (FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _59_269 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = _59_269.depth; tcenv = _59_269.tcenv; warn = _59_269.warn; cache = _59_269.cache; nolabels = _59_269.nolabels; use_zfuel_name = _59_269.use_zfuel_name; encode_non_total_function_typ = _59_269.encode_non_total_function_typ})))))

let push_typ_var : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_ToSMT_Term.term  ->  env_t = (fun env x t -> (let _59_274 = env
in {bindings = (Binding_tvar ((x, t)))::env.bindings; depth = _59_274.depth; tcenv = _59_274.tcenv; warn = _59_274.warn; cache = _59_274.cache; nolabels = _59_274.nolabels; use_zfuel_name = _59_274.use_zfuel_name; encode_non_total_function_typ = _59_274.encode_non_total_function_typ}))

let lookup_typ_var = (fun env a -> (match ((lookup_binding env (fun _59_4 -> (match (_59_4) with
| Binding_tvar (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _59_284 -> begin
None
end)))) with
| None -> begin
(let _162_356 = (let _162_355 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound type variable not found: %s" _162_355))
in (FStar_All.failwith _162_356))
end
| Some (b, t) -> begin
t
end))

let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Prims.strcat fname "@tok")
in (let _162_367 = (let _59_294 = env
in (let _162_366 = (let _162_365 = (let _162_364 = (let _162_363 = (let _162_362 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _162_361 -> Some (_162_361)) _162_362))
in (x, fname, _162_363, None))
in Binding_fvar (_162_364))
in (_162_365)::env.bindings)
in {bindings = _162_366; depth = _59_294.depth; tcenv = _59_294.tcenv; warn = _59_294.warn; cache = _59_294.cache; nolabels = _59_294.nolabels; use_zfuel_name = _59_294.use_zfuel_name; encode_non_total_function_typ = _59_294.encode_non_total_function_typ}))
in (fname, ftok, _162_367)))))

let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _59_5 -> (match (_59_5) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _59_306 -> begin
None
end))))

let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _162_378 = (let _162_377 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Name not found: %s" _162_377))
in (FStar_All.failwith _162_378))
end
| Some (s) -> begin
s
end))

let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (let _59_316 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _59_316.depth; tcenv = _59_316.tcenv; warn = _59_316.warn; cache = _59_316.cache; nolabels = _59_316.nolabels; use_zfuel_name = _59_316.use_zfuel_name; encode_non_total_function_typ = _59_316.encode_non_total_function_typ}))

let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (let _59_325 = (lookup_lid env x)
in (match (_59_325) with
| (t1, t2, _59_324) -> begin
(let t3 = (let _162_395 = (let _162_394 = (let _162_393 = (FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_162_393)::[])
in (f, _162_394))
in (FStar_ToSMT_Term.mkApp _162_395))
in (let _59_327 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _59_327.depth; tcenv = _59_327.tcenv; warn = _59_327.warn; cache = _59_327.cache; nolabels = _59_327.nolabels; use_zfuel_name = _59_327.use_zfuel_name; encode_non_total_function_typ = _59_327.encode_non_total_function_typ}))
end)))

let lookup_free_var = (fun env a -> (let _59_334 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_59_334) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
f
end
| _59_338 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (_59_342, fuel::[]) -> begin
if (let _162_399 = (let _162_398 = (FStar_ToSMT_Term.fv_of_term fuel)
in (FStar_All.pipe_right _162_398 Prims.fst))
in (FStar_Util.starts_with _162_399 "fuel")) then begin
(let _162_400 = (FStar_ToSMT_Term.mkFreeV (name, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_ApplyEF _162_400 fuel))
end else begin
t
end
end
| _59_348 -> begin
t
end)
end
| _59_350 -> begin
(let _162_402 = (let _162_401 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _162_401))
in (FStar_All.failwith _162_402))
end)
end)
end)))

let lookup_free_var_name = (fun env a -> (let _59_358 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_59_358) with
| (x, _59_355, _59_357) -> begin
x
end)))

let lookup_free_var_sym = (fun env a -> (let _59_364 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_59_364) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (g, zf); FStar_ToSMT_Term.hash = _59_368; FStar_ToSMT_Term.freevars = _59_366}) when env.use_zfuel_name -> begin
(g, zf)
end
| _59_376 -> begin
(match (sym) with
| None -> begin
(FStar_ToSMT_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _59_386 -> begin
(FStar_ToSMT_Term.Var (name), [])
end)
end)
end)
end)))

let new_typ_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Prims.strcat fname "@tok")
in (let _162_417 = (let _59_391 = env
in (let _162_416 = (let _162_415 = (let _162_414 = (let _162_413 = (let _162_412 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _162_411 -> Some (_162_411)) _162_412))
in (x, fname, _162_413))
in Binding_ftvar (_162_414))
in (_162_415)::env.bindings)
in {bindings = _162_416; depth = _59_391.depth; tcenv = _59_391.tcenv; warn = _59_391.warn; cache = _59_391.cache; nolabels = _59_391.nolabels; use_zfuel_name = _59_391.use_zfuel_name; encode_non_total_function_typ = _59_391.encode_non_total_function_typ}))
in (fname, ftok, _162_417)))))

let lookup_tlid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option) = (fun env a -> (match ((lookup_binding env (fun _59_6 -> (match (_59_6) with
| Binding_ftvar (b, t1, t2) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2))
end
| _59_402 -> begin
None
end)))) with
| None -> begin
(let _162_424 = (let _162_423 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Type name not found: %s" _162_423))
in (FStar_All.failwith _162_424))
end
| Some (s) -> begin
s
end))

let push_free_tvar : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (let _59_410 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _59_410.depth; tcenv = _59_410.tcenv; warn = _59_410.warn; cache = _59_410.cache; nolabels = _59_410.nolabels; use_zfuel_name = _59_410.use_zfuel_name; encode_non_total_function_typ = _59_410.encode_non_total_function_typ}))

let lookup_free_tvar = (fun env a -> (match ((let _162_435 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _162_435 Prims.snd))) with
| None -> begin
(let _162_437 = (let _162_436 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Type name not found: %s" _162_436))
in (FStar_All.failwith _162_437))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun env a -> (let _162_440 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _162_440 Prims.fst)))

let tok_of_name : env_t  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _59_7 -> (match (_59_7) with
| (Binding_fvar (_, nm', tok, _)) | (Binding_ftvar (_, nm', tok)) when (nm = nm') -> begin
tok
end
| _59_435 -> begin
None
end))))

let mkForall_fuel' = (fun n _59_440 -> (match (_59_440) with
| (pats, vars, body) -> begin
(let fallback = (fun _59_442 -> (match (()) with
| () -> begin
(FStar_ToSMT_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(let _59_445 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_59_445) with
| (fsym, fterm) -> begin
(let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var ("HasType"), args) -> begin
(FStar_ToSMT_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _59_455 -> begin
p
end)))))
in (let pats = (FStar_List.map add_fuel pats)
in (let body = (match (body.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, guard::body'::[]) -> begin
(let guard = (match (guard.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.And, guards) -> begin
(let _162_453 = (add_fuel guards)
in (FStar_ToSMT_Term.mk_and_l _162_453))
end
| _59_468 -> begin
(let _162_454 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _162_454 FStar_List.hd))
end)
in (FStar_ToSMT_Term.mkImp (guard, body')))
end
| _59_471 -> begin
body
end)
in (let vars = ((fsym, FStar_ToSMT_Term.Fuel_sort))::vars
in (FStar_ToSMT_Term.mkForall (pats, vars, body))))))
end))
end)
end))

let mkForall_fuel : (FStar_ToSMT_Term.pat Prims.list Prims.list * FStar_ToSMT_Term.fvs * FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term = (mkForall_fuel' 1)

let head_normal : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun env t -> (let t = (FStar_Absyn_Util.unmeta_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_refine (_)) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| (FStar_Absyn_Syntax.Typ_const (v)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (v); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _162_460 = (FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _162_460 FStar_Option.isNone))
end
| _59_509 -> begin
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

let trivial_post : (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.typ = (fun t -> (let _162_480 = (let _162_479 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (((FStar_Absyn_Syntax.null_v_binder t))::[], _162_479))
in (FStar_Absyn_Syntax.mk_Typ_lam _162_480 None t.FStar_Absyn_Syntax.pos)))

let mk_ApplyE : FStar_ToSMT_Term.term  ->  (Prims.string * FStar_ToSMT_Term.sort) Prims.list  ->  FStar_ToSMT_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _162_487 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyET out _162_487))
end
| FStar_ToSMT_Term.Fuel_sort -> begin
(let _162_488 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEF out _162_488))
end
| _59_526 -> begin
(let _162_489 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEE out _162_489))
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
(let _162_502 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTT out _162_502))
end
| _59_541 -> begin
(let _162_503 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTE out _162_503))
end)) t)))

let mk_ApplyT_args : FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list  ->  FStar_ToSMT_Term.term = (fun t args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out arg -> (match (arg) with
| FStar_Util.Inl (t) -> begin
(FStar_ToSMT_Term.mk_ApplyTT out t)
end
| FStar_Util.Inr (e) -> begin
(FStar_ToSMT_Term.mk_ApplyTE out e)
end)) t)))

let is_app : FStar_ToSMT_Term.op  ->  Prims.bool = (fun _59_8 -> (match (_59_8) with
| (FStar_ToSMT_Term.Var ("ApplyTT")) | (FStar_ToSMT_Term.Var ("ApplyTE")) | (FStar_ToSMT_Term.Var ("ApplyET")) | (FStar_ToSMT_Term.Var ("ApplyEE")) -> begin
true
end
| _59_560 -> begin
false
end))

let is_eta : env_t  ->  FStar_ToSMT_Term.fv Prims.list  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term Prims.option = (fun env vars t -> (let rec aux = (fun t xs -> (match ((t.FStar_ToSMT_Term.tm, xs)) with
| (FStar_ToSMT_Term.App (app, f::{FStar_ToSMT_Term.tm = FStar_ToSMT_Term.FreeV (y); FStar_ToSMT_Term.hash = _59_571; FStar_ToSMT_Term.freevars = _59_569}::[]), x::xs) when ((is_app app) && (FStar_ToSMT_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var (f), args), _59_589) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (fv) -> begin
(FStar_ToSMT_Term.fv_eq fv v)
end
| _59_596 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_59_598, []) -> begin
(let fvs = (FStar_ToSMT_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_ToSMT_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _59_604 -> begin
None
end))
in (aux t (FStar_List.rev vars))))

type label =
(FStar_ToSMT_Term.fv * Prims.string * FStar_Range.range)

type labels =
label Prims.list

type pattern =
{pat_vars : (FStar_Absyn_Syntax.either_var * FStar_ToSMT_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t); guard : FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term; projections : FStar_ToSMT_Term.term  ->  (FStar_Absyn_Syntax.either_var * FStar_ToSMT_Term.term) Prims.list}

let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))

exception Let_rec_unencodeable

let is_Let_rec_unencodeable : Prims.exn  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable -> begin
true
end
| _ -> begin
false
end))

let encode_const : FStar_Const.sconst  ->  FStar_ToSMT_Term.term = (fun _59_9 -> (match (_59_9) with
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
(let _162_559 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_ToSMT_Term.boxInt _162_559))
end
| FStar_Const.Const_uint8 (i) -> begin
(let _162_560 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_ToSMT_Term.boxInt _162_560))
end
| FStar_Const.Const_int (i) -> begin
(let _162_561 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _162_561))
end
| FStar_Const.Const_int32 (i) -> begin
(let _162_565 = (let _162_564 = (let _162_563 = (let _162_562 = (FStar_ToSMT_Term.mkInteger32 i)
in (FStar_ToSMT_Term.boxInt _162_562))
in (_162_563)::[])
in ("FStar.Int32.Int32", _162_564))
in (FStar_ToSMT_Term.mkApp _162_565))
end
| FStar_Const.Const_string (bytes, _59_626) -> begin
(let _162_566 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _162_566))
end
| c -> begin
(let _162_568 = (let _162_567 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s\n" _162_567))
in (FStar_All.failwith _162_568))
end))

let as_function_typ : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t0 -> (let rec aux = (fun norm t -> (let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_59_637) -> begin
t
end
| FStar_Absyn_Syntax.Typ_refine (_59_640) -> begin
(let _162_577 = (FStar_Absyn_Util.unrefine t)
in (aux true _162_577))
end
| _59_643 -> begin
if norm then begin
(let _162_578 = (whnf env t)
in (aux false _162_578))
end else begin
(let _162_581 = (let _162_580 = (FStar_Range.string_of_range t0.FStar_Absyn_Syntax.pos)
in (let _162_579 = (FStar_Absyn_Print.typ_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _162_580 _162_579)))
in (FStar_All.failwith _162_581))
end
end)))
in (aux true t0)))

let rec encode_knd_term : FStar_Absyn_Syntax.knd  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun k env -> (match ((let _162_618 = (FStar_Absyn_Util.compress_kind k)
in _162_618.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
(FStar_ToSMT_Term.mk_Kind_type, [])
end
| FStar_Absyn_Syntax.Kind_abbrev (_59_648, k0) -> begin
(let _59_652 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _162_620 = (FStar_Absyn_Print.kind_to_string k)
in (let _162_619 = (FStar_Absyn_Print.kind_to_string k0)
in (FStar_Util.print2 "Encoding kind abbrev %s, expanded to %s\n" _162_620 _162_619)))
end else begin
()
end
in (encode_knd_term k0 env))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, _59_656) -> begin
(let _162_622 = (let _162_621 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Kind_uvar _162_621))
in (_162_622, []))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, kbody) -> begin
(let tsym = (let _162_623 = (varops.fresh "t")
in (_162_623, FStar_ToSMT_Term.Type_sort))
in (let t = (FStar_ToSMT_Term.mkFreeV tsym)
in (let _59_671 = (encode_binders None bs env)
in (match (_59_671) with
| (vars, guards, env', decls, _59_670) -> begin
(let app = (mk_ApplyT t vars)
in (let _59_675 = (encode_knd kbody env' app)
in (match (_59_675) with
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
| _59_694 -> begin
(let _162_632 = (let _162_631 = (let _162_630 = (FStar_ToSMT_Term.mk_PreKind app)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _162_630))
in (_162_631, body))
in (FStar_ToSMT_Term.mkAnd _162_632))
end)
in (let _162_634 = (let _162_633 = (FStar_ToSMT_Term.mkImp (g, body))
in (((app)::[])::[], (x)::[], _162_633))
in (FStar_ToSMT_Term.mkForall _162_634)))))
end
| _59_697 -> begin
(FStar_All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (let k_interp = (aux t vars guards)
in (let cvars = (let _162_636 = (FStar_ToSMT_Term.free_variables k_interp)
in (FStar_All.pipe_right _162_636 (FStar_List.filter (fun _59_702 -> (match (_59_702) with
| (x, _59_701) -> begin
(x <> (Prims.fst tsym))
end)))))
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (k', sorts, _59_708) -> begin
(let _162_639 = (let _162_638 = (let _162_637 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (k', _162_637))
in (FStar_ToSMT_Term.mkApp _162_638))
in (_162_639, []))
end
| None -> begin
(let ksym = (varops.fresh "Kind_arrow")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _162_640 = (FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_162_640))
end else begin
None
end
in (let kdecl = FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, FStar_ToSMT_Term.Kind_sort, caption))
in (let k = (let _162_642 = (let _162_641 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _162_641))
in (FStar_ToSMT_Term.mkApp _162_642))
in (let t_has_k = (FStar_ToSMT_Term.mk_HasKind t k)
in (let k_interp = (let _162_651 = (let _162_650 = (let _162_649 = (let _162_648 = (let _162_647 = (let _162_646 = (let _162_645 = (let _162_644 = (let _162_643 = (FStar_ToSMT_Term.mk_PreKind t)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _162_643))
in (_162_644, k_interp))
in (FStar_ToSMT_Term.mkAnd _162_645))
in (t_has_k, _162_646))
in (FStar_ToSMT_Term.mkIff _162_647))
in (((t_has_k)::[])::[], (tsym)::cvars, _162_648))
in (FStar_ToSMT_Term.mkForall _162_649))
in (_162_650, Some ((Prims.strcat ksym " interpretation"))))
in FStar_ToSMT_Term.Assume (_162_651))
in (let k_decls = (FStar_List.append (FStar_List.append decls decls') ((kdecl)::(k_interp)::[]))
in (let _59_720 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _59_723 -> begin
(let _162_653 = (let _162_652 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.format1 "Unknown kind: %s" _162_652))
in (FStar_All.failwith _162_653))
end))
and encode_knd : FStar_Absyn_Syntax.knd  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decl Prims.list) = (fun k env t -> (let _59_729 = (encode_knd_term k env)
in (match (_59_729) with
| (k, decls) -> begin
(let _162_657 = (FStar_ToSMT_Term.mk_HasKind t k)
in (_162_657, decls))
end)))
and encode_binders : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.binders  ->  env_t  ->  (FStar_ToSMT_Term.fv Prims.list * FStar_ToSMT_Term.term Prims.list * env_t * FStar_ToSMT_Term.decls_t * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list) = (fun fuel_opt bs env -> (let _59_733 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _162_661 = (FStar_Absyn_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _162_661))
end else begin
()
end
in (let _59_783 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _59_740 b -> (match (_59_740) with
| (vars, guards, env, decls, names) -> begin
(let _59_777 = (match ((Prims.fst b)) with
| FStar_Util.Inl ({FStar_Absyn_Syntax.v = a; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _59_743}) -> begin
(let a = (unmangle a)
in (let _59_752 = (gen_typ_var env a)
in (match (_59_752) with
| (aasym, aa, env') -> begin
(let _59_753 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _162_665 = (FStar_Absyn_Print.strBvd a)
in (let _162_664 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.print3 "Encoding type binder %s (%s) at kind %s\n" _162_665 aasym _162_664)))
end else begin
()
end
in (let _59_757 = (encode_knd k env aa)
in (match (_59_757) with
| (guard_a_k, decls') -> begin
((aasym, FStar_ToSMT_Term.Type_sort), guard_a_k, env', decls', FStar_Util.Inl (a))
end)))
end)))
end
| FStar_Util.Inr ({FStar_Absyn_Syntax.v = x; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _59_759}) -> begin
(let x = (unmangle x)
in (let _59_768 = (gen_term_var env x)
in (match (_59_768) with
| (xxsym, xx, env') -> begin
(let _59_771 = (let _162_666 = (norm_t env t)
in (encode_typ_pred fuel_opt _162_666 env xx))
in (match (_59_771) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_ToSMT_Term.Term_sort), guard_x_t, env', decls', FStar_Util.Inr (x))
end))
end)))
end)
in (match (_59_777) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_59_783) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_typ_pred : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun fuel_opt t env e -> (let t = (FStar_Absyn_Util.compress_typ t)
in (let _59_791 = (encode_typ_term t env)
in (match (_59_791) with
| (t, decls) -> begin
(let _162_671 = (FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_162_671, decls))
end))))
and encode_typ_pred' : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun fuel_opt t env e -> (let t = (FStar_Absyn_Util.compress_typ t)
in (let _59_799 = (encode_typ_term t env)
in (match (_59_799) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _162_676 = (FStar_ToSMT_Term.mk_HasTypeZ e t)
in (_162_676, decls))
end
| Some (f) -> begin
(let _162_677 = (FStar_ToSMT_Term.mk_HasTypeFuel f e t)
in (_162_677, decls))
end)
end))))
and encode_typ_term : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun t env -> (let t0 = (FStar_Absyn_Util.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _162_680 = (lookup_typ_var env a)
in (_162_680, []))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _162_681 = (lookup_free_tvar env fv)
in (_162_681, []))
end
| FStar_Absyn_Syntax.Typ_fun (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (FStar_Absyn_Util.is_tot_or_gtot_comp res)) then begin
(let _59_820 = (encode_binders None binders env)
in (match (_59_820) with
| (vars, guards, env', decls, _59_819) -> begin
(let fsym = (let _162_682 = (varops.fresh "f")
in (_162_682, FStar_ToSMT_Term.Term_sort))
in (let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (let app = (mk_ApplyE f vars)
in (let _59_826 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_59_826) with
| (pre_opt, res_t) -> begin
(let _59_829 = (encode_typ_pred None res_t env' app)
in (match (_59_829) with
| (res_pred, decls') -> begin
(let _59_838 = (match (pre_opt) with
| None -> begin
(let _162_683 = (FStar_ToSMT_Term.mk_and_l guards)
in (_162_683, decls))
end
| Some (pre) -> begin
(let _59_835 = (encode_formula pre env')
in (match (_59_835) with
| (guard, decls0) -> begin
(let _162_684 = (FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_162_684, (FStar_List.append decls decls0)))
end))
end)
in (match (_59_838) with
| (guards, guard_decls) -> begin
(let t_interp = (let _162_686 = (let _162_685 = (FStar_ToSMT_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _162_685))
in (FStar_ToSMT_Term.mkForall _162_686))
in (let cvars = (let _162_688 = (FStar_ToSMT_Term.free_variables t_interp)
in (FStar_All.pipe_right _162_688 (FStar_List.filter (fun _59_843 -> (match (_59_843) with
| (x, _59_842) -> begin
(x <> (Prims.fst fsym))
end)))))
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t', sorts, _59_849) -> begin
(let _162_691 = (let _162_690 = (let _162_689 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t', _162_689))
in (FStar_ToSMT_Term.mkApp _162_690))
in (_162_691, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _162_692 = (FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_162_692))
end else begin
None
end
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, caption))
in (let t = (let _162_694 = (let _162_693 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _162_693))
in (FStar_ToSMT_Term.mkApp _162_694))
in (let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = (let _162_696 = (let _162_695 = (FStar_ToSMT_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_162_695, Some ((Prims.strcat tsym " kinding"))))
in FStar_ToSMT_Term.Assume (_162_696))
in (let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (let f_has_t_z = (FStar_ToSMT_Term.mk_HasTypeZ f t)
in (let pre_typing = (let _162_703 = (let _162_702 = (let _162_701 = (let _162_700 = (let _162_699 = (let _162_698 = (let _162_697 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _162_697))
in (f_has_t, _162_698))
in (FStar_ToSMT_Term.mkImp _162_699))
in (((f_has_t)::[])::[], (fsym)::cvars, _162_700))
in (mkForall_fuel _162_701))
in (_162_702, Some ("pre-typing for functions")))
in FStar_ToSMT_Term.Assume (_162_703))
in (let t_interp = (let _162_707 = (let _162_706 = (let _162_705 = (let _162_704 = (FStar_ToSMT_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _162_704))
in (FStar_ToSMT_Term.mkForall _162_705))
in (_162_706, Some ((Prims.strcat tsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_162_707))
in (let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (let _59_865 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(let tsym = (varops.fresh "Non_total_Typ_fun")
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, [], FStar_ToSMT_Term.Type_sort, None))
in (let t = (FStar_ToSMT_Term.mkApp (tsym, []))
in (let t_kinding = (let _162_709 = (let _162_708 = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (_162_708, None))
in FStar_ToSMT_Term.Assume (_162_709))
in (let fsym = ("f", FStar_ToSMT_Term.Term_sort)
in (let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = (let _162_716 = (let _162_715 = (let _162_714 = (let _162_713 = (let _162_712 = (let _162_711 = (let _162_710 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _162_710))
in (f_has_t, _162_711))
in (FStar_ToSMT_Term.mkImp _162_712))
in (((f_has_t)::[])::[], (fsym)::[], _162_713))
in (mkForall_fuel _162_714))
in (_162_715, Some ("pre-typing")))
in FStar_ToSMT_Term.Assume (_162_716))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end
| FStar_Absyn_Syntax.Typ_refine (_59_876) -> begin
(let _59_895 = (match ((FStar_Tc_Normalize.normalize_refinement [] env.tcenv t0)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_refine (x, f); FStar_Absyn_Syntax.tk = _59_885; FStar_Absyn_Syntax.pos = _59_883; FStar_Absyn_Syntax.fvs = _59_881; FStar_Absyn_Syntax.uvs = _59_879} -> begin
(x, f)
end
| _59_892 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_59_895) with
| (x, f) -> begin
(let _59_898 = (encode_typ_term x.FStar_Absyn_Syntax.sort env)
in (match (_59_898) with
| (base_t, decls) -> begin
(let _59_902 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_59_902) with
| (x, xtm, env') -> begin
(let _59_905 = (encode_formula f env')
in (match (_59_905) with
| (refinement, decls') -> begin
(let _59_908 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_59_908) with
| (fsym, fterm) -> begin
(let encoding = (let _162_718 = (let _162_717 = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_162_717, refinement))
in (FStar_ToSMT_Term.mkAnd _162_718))
in (let cvars = (let _162_720 = (FStar_ToSMT_Term.free_variables encoding)
in (FStar_All.pipe_right _162_720 (FStar_List.filter (fun _59_913 -> (match (_59_913) with
| (y, _59_912) -> begin
((y <> x) && (y <> fsym))
end)))))
in (let xfv = (x, FStar_ToSMT_Term.Term_sort)
in (let ffv = (fsym, FStar_ToSMT_Term.Fuel_sort)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _59_920, _59_922) -> begin
(let _162_723 = (let _162_722 = (let _162_721 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t, _162_721))
in (FStar_ToSMT_Term.mkApp _162_722))
in (_162_723, []))
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, None))
in (let t = (let _162_725 = (let _162_724 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _162_724))
in (FStar_ToSMT_Term.mkApp _162_725))
in (let x_has_t = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (FStar_ToSMT_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (let assumption = (let _162_727 = (let _162_726 = (FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _162_726))
in (FStar_ToSMT_Term.mkForall _162_727))
in (let t_decls = (let _162_734 = (let _162_733 = (let _162_732 = (let _162_731 = (let _162_730 = (let _162_729 = (let _162_728 = (FStar_Absyn_Print.typ_to_string t0)
in Some (_162_728))
in (assumption, _162_729))
in FStar_ToSMT_Term.Assume (_162_730))
in (_162_731)::[])
in (FStar_ToSMT_Term.Assume ((t_kinding, None)))::_162_732)
in (tdecl)::_162_733)
in (FStar_List.append (FStar_List.append decls decls') _162_734))
in (let _59_935 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let ttm = (let _162_735 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _162_735))
in (let _59_944 = (encode_knd k env ttm)
in (match (_59_944) with
| (t_has_k, decls) -> begin
(let d = FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(let is_full_app = (fun _59_951 -> (match (()) with
| () -> begin
(let kk = (FStar_Tc_Recheck.recompute_kind head)
in (let _59_956 = (FStar_Absyn_Util.kind_formals kk)
in (match (_59_956) with
| (formals, _59_955) -> begin
((FStar_List.length formals) = (FStar_List.length args))
end)))
end))
in (let head = (FStar_Absyn_Util.compress_typ head)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let head = (lookup_typ_var env a)
in (let _59_963 = (encode_args args env)
in (match (_59_963) with
| (args, decls) -> begin
(let t = (mk_ApplyT_args head args)
in (t, decls))
end)))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _59_969 = (encode_args args env)
in (match (_59_969) with
| (args, decls) -> begin
if (is_full_app ()) then begin
(let head = (lookup_free_tvar_name env fv)
in (let t = (let _162_740 = (let _162_739 = (FStar_List.map (fun _59_10 -> (match (_59_10) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (head, _162_739))
in (FStar_ToSMT_Term.mkApp _162_740))
in (t, decls)))
end else begin
(let head = (lookup_free_tvar env fv)
in (let t = (mk_ApplyT_args head args)
in (t, decls)))
end
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(let ttm = (let _162_741 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _162_741))
in (let _59_985 = (encode_knd k env ttm)
in (match (_59_985) with
| (t_has_k, decls) -> begin
(let d = FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| _59_988 -> begin
(let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, body) -> begin
(let _59_1000 = (encode_binders None bs env)
in (match (_59_1000) with
| (vars, guards, env, decls, _59_999) -> begin
(let _59_1003 = (encode_typ_term body env)
in (match (_59_1003) with
| (body, decls') -> begin
(let key_body = (let _162_745 = (let _162_744 = (let _162_743 = (let _162_742 = (FStar_ToSMT_Term.mk_and_l guards)
in (_162_742, body))
in (FStar_ToSMT_Term.mkImp _162_743))
in ([], vars, _162_744))
in (FStar_ToSMT_Term.mkForall _162_745))
in (let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _59_1009, _59_1011) -> begin
(let _162_748 = (let _162_747 = (let _162_746 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _162_746))
in (FStar_ToSMT_Term.mkApp _162_747))
in (_162_748, []))
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
in (let t = (let _162_750 = (let _162_749 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _162_749))
in (FStar_ToSMT_Term.mkApp _162_750))
in (let app = (mk_ApplyT t vars)
in (let interp = (let _162_757 = (let _162_756 = (let _162_755 = (let _162_754 = (let _162_753 = (let _162_752 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _162_751 = (FStar_ToSMT_Term.mkEq (app, body))
in (_162_752, _162_751)))
in (FStar_ToSMT_Term.mkImp _162_753))
in (((app)::[])::[], (FStar_List.append vars cvars), _162_754))
in (FStar_ToSMT_Term.mkForall _162_755))
in (_162_756, Some ("Typ_lam interpretation")))
in FStar_ToSMT_Term.Assume (_162_757))
in (let kinding = (let _59_1026 = (let _162_758 = (FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _162_758 env t))
in (match (_59_1026) with
| (ktm, decls'') -> begin
(let _162_762 = (let _162_761 = (let _162_760 = (let _162_759 = (FStar_ToSMT_Term.mkForall (((t)::[])::[], cvars, ktm))
in (_162_759, Some ("Typ_lam kinding")))
in FStar_ToSMT_Term.Assume (_162_760))
in (_162_761)::[])
in (FStar_List.append decls'' _162_762))
end))
in (let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(interp)::kinding))
in (let _59_1029 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))
end)
end))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _59_1033) -> begin
(encode_typ_term t env)
end
| FStar_Absyn_Syntax.Typ_meta (_59_1037) -> begin
(let _162_763 = (FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _162_763 env))
end
| (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _162_768 = (let _162_767 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Absyn_Syntax.pos)
in (let _162_766 = (FStar_Absyn_Print.tag_of_typ t0)
in (let _162_765 = (FStar_Absyn_Print.typ_to_string t0)
in (let _162_764 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _162_767 _162_766 _162_765 _162_764)))))
in (FStar_All.failwith _162_768))
end)))
and encode_exp : FStar_Absyn_Syntax.exp  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun e env -> (let e = (FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_59_1048) -> begin
(let _162_771 = (FStar_Absyn_Util.compress_exp e)
in (encode_exp _162_771 env))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Absyn_Syntax.Exp_fvar (v, _59_1055) -> begin
(let _162_772 = (lookup_free_var env v)
in (_162_772, []))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _162_773 = (encode_const c)
in (_162_773, []))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _59_1063) -> begin
(let _59_1066 = (FStar_ST.op_Colon_Equals e.FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _59_1070)) -> begin
(encode_exp e env)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, _59_1076) -> begin
(let e = (let _162_774 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Exp_uvar _162_774))
in (e, []))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(let fallback = (fun _59_1085 -> (match (()) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = FStar_ToSMT_Term.DeclFun ((f, [], FStar_ToSMT_Term.Term_sort, None))
in (let _162_777 = (FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
in (_162_777, (decl)::[]))))
end))
in (match ((FStar_ST.read e.FStar_Absyn_Syntax.tk)) with
| None -> begin
(let _59_1089 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
if (let _162_778 = (FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (FStar_All.pipe_left Prims.op_Negation _162_778)) then begin
(fallback ())
end else begin
(let tfun = (as_function_typ env tfun)
in (match (tfun.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(let nformals = (FStar_List.length bs')
in if ((nformals < (FStar_List.length bs)) && (FStar_Absyn_Util.is_total_comp c)) then begin
(let _59_1101 = (FStar_Util.first_N nformals bs)
in (match (_59_1101) with
| (bs0, rest) -> begin
(let res_t = (match ((FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s (FStar_Absyn_Util.comp_result c))
end
| _59_1105 -> begin
(FStar_All.failwith "Impossible")
end)
in (let e = (let _162_780 = (let _162_779 = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.FStar_Absyn_Syntax.pos)
in (bs0, _162_779))
in (FStar_Absyn_Syntax.mk_Exp_abs _162_780 (Some (tfun)) e0.FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end else begin
(let _59_1114 = (encode_binders None bs env)
in (match (_59_1114) with
| (vars, guards, envbody, decls, _59_1113) -> begin
(let _59_1117 = (encode_exp body envbody)
in (match (_59_1117) with
| (body, decls') -> begin
(let key_body = (let _162_784 = (let _162_783 = (let _162_782 = (let _162_781 = (FStar_ToSMT_Term.mk_and_l guards)
in (_162_781, body))
in (FStar_ToSMT_Term.mkImp _162_782))
in ([], vars, _162_783))
in (FStar_ToSMT_Term.mkForall _162_784))
in (let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _59_1123, _59_1125) -> begin
(let _162_787 = (let _162_786 = (let _162_785 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _162_785))
in (FStar_ToSMT_Term.mkApp _162_786))
in (_162_787, []))
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
in (let f = (let _162_789 = (let _162_788 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _162_788))
in (FStar_ToSMT_Term.mkApp _162_789))
in (let app = (mk_ApplyE f vars)
in (let _59_1139 = (encode_typ_pred None tfun env f)
in (match (_59_1139) with
| (f_has_t, decls'') -> begin
(let typing_f = (let _162_791 = (let _162_790 = (FStar_ToSMT_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_162_790, Some ((Prims.strcat fsym " typing"))))
in FStar_ToSMT_Term.Assume (_162_791))
in (let interp_f = (let _162_798 = (let _162_797 = (let _162_796 = (let _162_795 = (let _162_794 = (let _162_793 = (FStar_ToSMT_Term.mk_IsTyped app)
in (let _162_792 = (FStar_ToSMT_Term.mkEq (app, body))
in (_162_793, _162_792)))
in (FStar_ToSMT_Term.mkImp _162_794))
in (((app)::[])::[], (FStar_List.append vars cvars), _162_795))
in (FStar_ToSMT_Term.mkForall _162_796))
in (_162_797, Some ((Prims.strcat fsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_162_798))
in (let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (let _59_1143 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end)))))))
end)
end))))
end))
end))
end)
end
| _59_1146 -> begin
(FStar_All.failwith "Impossible")
end))
end
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (l, _59_1157); FStar_Absyn_Syntax.tk = _59_1154; FStar_Absyn_Syntax.pos = _59_1152; FStar_Absyn_Syntax.fvs = _59_1150; FStar_Absyn_Syntax.uvs = _59_1148}, (FStar_Util.Inl (_59_1172), _59_1175)::(FStar_Util.Inr (v1), _59_1169)::(FStar_Util.Inr (v2), _59_1164)::[]) when (FStar_Ident.lid_equals l.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
(let _59_1182 = (encode_exp v1 env)
in (match (_59_1182) with
| (v1, decls1) -> begin
(let _59_1185 = (encode_exp v2 env)
in (match (_59_1185) with
| (v2, decls2) -> begin
(let _162_799 = (FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_162_799, (FStar_List.append decls1 decls2)))
end))
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_59_1195); FStar_Absyn_Syntax.tk = _59_1193; FStar_Absyn_Syntax.pos = _59_1191; FStar_Absyn_Syntax.fvs = _59_1189; FStar_Absyn_Syntax.uvs = _59_1187}, _59_1199) -> begin
(let _162_800 = (whnf_e env e)
in (encode_exp _162_800 env))
end
| FStar_Absyn_Syntax.Exp_app (head, args_e) -> begin
(let _59_1208 = (encode_args args_e env)
in (match (_59_1208) with
| (args, decls) -> begin
(let encode_partial_app = (fun ht_opt -> (let _59_1213 = (encode_exp head env)
in (match (_59_1213) with
| (head, decls') -> begin
(let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(let _59_1222 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_59_1222) with
| (formals, rest) -> begin
(let subst = (FStar_Absyn_Util.formals_for_actuals formals args_e)
in (let ty = (let _162_803 = (FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (FStar_Absyn_Syntax.ktype)) e0.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _162_803 (FStar_Absyn_Util.subst_typ subst)))
in (let _59_1227 = (encode_typ_pred None ty env app_tm)
in (match (_59_1227) with
| (has_type, decls'') -> begin
(let cvars = (FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = (let _162_805 = (let _162_804 = (FStar_ToSMT_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_162_804, None))
in FStar_ToSMT_Term.Assume (_162_805))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun fv -> (let _59_1234 = (lookup_free_var_sym env fv)
in (match (_59_1234) with
| (fname, fuel_args) -> begin
(let tm = (let _162_811 = (let _162_810 = (let _162_809 = (FStar_List.map (fun _59_11 -> (match (_59_11) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (FStar_List.append fuel_args _162_809))
in (fname, _162_810))
in (FStar_ToSMT_Term.mkApp' _162_811))
in (tm, decls))
end)))
in (let head = (FStar_Absyn_Util.compress_exp head)
in (let _59_1241 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("186"))) then begin
(let _162_813 = (FStar_Absyn_Print.exp_to_string head)
in (let _162_812 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.print2 "Recomputing type for %s\nFull term is %s\n" _162_813 _162_812)))
end else begin
()
end
in (let head_type = (let _162_816 = (let _162_815 = (let _162_814 = (FStar_Tc_Recheck.recompute_typ head)
in (FStar_Absyn_Util.unrefine _162_814))
in (whnf env _162_815))
in (FStar_All.pipe_left FStar_Absyn_Util.unrefine _162_816))
in (let _59_1244 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _162_819 = (FStar_Absyn_Print.exp_to_string head)
in (let _162_818 = (FStar_Absyn_Print.tag_of_exp head)
in (let _162_817 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.print3 "Recomputed type of head %s (%s) to be %s\n" _162_819 _162_818 _162_817))))
end else begin
()
end
in (match ((FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _162_823 = (let _162_822 = (FStar_Range.string_of_range e0.FStar_Absyn_Syntax.pos)
in (let _162_821 = (FStar_Absyn_Print.exp_to_string e0)
in (let _162_820 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.format3 "(%s) term is %s; head type is %s\n" _162_822 _162_821 _162_820))))
in (FStar_All.failwith _162_823))
end
| Some (formals, c) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _59_1253) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _59_1257 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some ((formals, c))))
end else begin
(encode_partial_app None)
end
end)
end)))))))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_59_1266); FStar_Absyn_Syntax.lbtyp = _59_1264; FStar_Absyn_Syntax.lbeff = _59_1262; FStar_Absyn_Syntax.lbdef = _59_1260}::[]), _59_1272) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = t1; FStar_Absyn_Syntax.lbeff = _59_1278; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(let _59_1290 = (encode_exp e1 env)
in (match (_59_1290) with
| (ee1, decls1) -> begin
(let env' = (push_term_var env x ee1)
in (let _59_1294 = (encode_exp e2 env')
in (match (_59_1294) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let (_59_1296) -> begin
(let _59_1298 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (let e = (varops.fresh "let-rec")
in (let decl_e = FStar_ToSMT_Term.DeclFun ((e, [], FStar_ToSMT_Term.Term_sort, None))
in (let _162_824 = (FStar_ToSMT_Term.mkFreeV (e, FStar_ToSMT_Term.Term_sort))
in (_162_824, (decl_e)::[])))))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(let _59_1308 = (encode_exp e env)
in (match (_59_1308) with
| (scr, decls) -> begin
(let _59_1348 = (FStar_List.fold_right (fun _59_1312 _59_1315 -> (match ((_59_1312, _59_1315)) with
| ((p, w, br), (else_case, decls)) -> begin
(let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _59_1319 _59_1322 -> (match ((_59_1319, _59_1322)) with
| ((env0, pattern), (else_case, decls)) -> begin
(let guard = (pattern.guard scr)
in (let projections = (pattern.projections scr)
in (let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _59_1328 -> (match (_59_1328) with
| (x, t) -> begin
(match (x) with
| FStar_Util.Inl (a) -> begin
(push_typ_var env a.FStar_Absyn_Syntax.v t)
end
| FStar_Util.Inr (x) -> begin
(push_term_var env x.FStar_Absyn_Syntax.v t)
end)
end)) env))
in (let _59_1342 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(let _59_1339 = (encode_exp w env)
in (match (_59_1339) with
| (w, decls2) -> begin
(let _162_835 = (let _162_834 = (let _162_833 = (let _162_832 = (let _162_831 = (FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
in (w, _162_831))
in (FStar_ToSMT_Term.mkEq _162_832))
in (guard, _162_833))
in (FStar_ToSMT_Term.mkAnd _162_834))
in (_162_835, decls2))
end))
end)
in (match (_59_1342) with
| (guard, decls2) -> begin
(let _59_1345 = (encode_exp br env)
in (match (_59_1345) with
| (br, decls3) -> begin
(let _162_836 = (FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_162_836, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end)) pats (FStar_ToSMT_Term.mk_Term_unit, decls))
in (match (_59_1348) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (_59_1350) -> begin
(let _162_839 = (let _162_838 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _162_837 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "(%s): Impossible: encode_exp got %s" _162_838 _162_837)))
in (FStar_All.failwith _162_839))
end))))
and encode_pat : env_t  ->  FStar_Absyn_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _59_1357 -> begin
(let _162_842 = (encode_one_pat env pat)
in (_162_842)::[])
end))
and encode_one_pat : env_t  ->  FStar_Absyn_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (let _59_1360 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _162_845 = (FStar_Absyn_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _162_845))
end else begin
()
end
in (let _59_1364 = (FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_59_1364) with
| (vars, pat_exp_or_typ) -> begin
(let _59_1385 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _59_1367 v -> (match (_59_1367) with
| (env, vars) -> begin
(match (v) with
| FStar_Util.Inl (a) -> begin
(let _59_1375 = (gen_typ_var env a.FStar_Absyn_Syntax.v)
in (match (_59_1375) with
| (aa, _59_1373, env) -> begin
(env, ((v, (aa, FStar_ToSMT_Term.Type_sort)))::vars)
end))
end
| FStar_Util.Inr (x) -> begin
(let _59_1382 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_59_1382) with
| (xx, _59_1380, env) -> begin
(env, ((v, (xx, FStar_ToSMT_Term.Term_sort)))::vars)
end))
end)
end)) (env, [])))
in (match (_59_1385) with
| (env, vars) -> begin
(let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_59_1390) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
FStar_ToSMT_Term.mkTrue
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _162_853 = (let _162_852 = (encode_const c)
in (scrutinee, _162_852))
in (FStar_ToSMT_Term.mkEq _162_853))
end
| FStar_Absyn_Syntax.Pat_cons (f, _59_1414, args) -> begin
(let is_f = (mk_data_tester env f.FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _59_1423 -> (match (_59_1423) with
| (arg, _59_1422) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _162_856 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _162_856)))
end))))
in (FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_59_1430) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _)) | (FStar_Absyn_Syntax.Pat_var (x)) | (FStar_Absyn_Syntax.Pat_wild (x)) -> begin
((FStar_Util.Inr (x), scrutinee))::[]
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _)) | (FStar_Absyn_Syntax.Pat_tvar (a)) | (FStar_Absyn_Syntax.Pat_twild (a)) -> begin
((FStar_Util.Inl (a), scrutinee))::[]
end
| FStar_Absyn_Syntax.Pat_constant (_59_1447) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_cons (f, _59_1451, args) -> begin
(let _162_864 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _59_1459 -> (match (_59_1459) with
| (arg, _59_1458) -> begin
(let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _162_863 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _162_863)))
end))))
in (FStar_All.pipe_right _162_864 FStar_List.flatten))
end))
in (let pat_term = (fun _59_1462 -> (match (()) with
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
and encode_args : FStar_Absyn_Syntax.args  ->  env_t  ->  ((FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list * FStar_ToSMT_Term.decls_t) = (fun l env -> (let _59_1492 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _59_1472 x -> (match (_59_1472) with
| (tms, decls) -> begin
(match (x) with
| (FStar_Util.Inl (t), _59_1477) -> begin
(let _59_1481 = (encode_typ_term t env)
in (match (_59_1481) with
| (t, decls') -> begin
((FStar_Util.Inl (t))::tms, (FStar_List.append decls decls'))
end))
end
| (FStar_Util.Inr (e), _59_1485) -> begin
(let _59_1489 = (encode_exp e env)
in (match (_59_1489) with
| (t, decls') -> begin
((FStar_Util.Inr (t))::tms, (FStar_List.append decls decls'))
end))
end)
end)) ([], [])))
in (match (_59_1492) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_formula : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun phi env -> (let _59_1498 = (encode_formula_with_labels phi env)
in (match (_59_1498) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _59_1501 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.exp Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun induction_on new_pats t env -> (let rec list_elements = (fun e -> (match ((let _162_879 = (FStar_Absyn_Util.unmeta_exp e)
in _162_879.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _59_1518); FStar_Absyn_Syntax.tk = _59_1515; FStar_Absyn_Syntax.pos = _59_1513; FStar_Absyn_Syntax.fvs = _59_1511; FStar_Absyn_Syntax.uvs = _59_1509}, _59_1523) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.nil_lid) -> begin
[]
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _59_1536); FStar_Absyn_Syntax.tk = _59_1533; FStar_Absyn_Syntax.pos = _59_1531; FStar_Absyn_Syntax.fvs = _59_1529; FStar_Absyn_Syntax.uvs = _59_1527}, _59_1551::(FStar_Util.Inr (hd), _59_1548)::(FStar_Util.Inr (tl), _59_1543)::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(let _162_880 = (list_elements tl)
in (hd)::_162_880)
end
| _59_1556 -> begin
(let _59_1557 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (let v_or_t_pat = (fun p -> (match ((let _162_883 = (FStar_Absyn_Util.unmeta_exp p)
in _162_883.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _59_1571); FStar_Absyn_Syntax.tk = _59_1568; FStar_Absyn_Syntax.pos = _59_1566; FStar_Absyn_Syntax.fvs = _59_1564; FStar_Absyn_Syntax.uvs = _59_1562}, (FStar_Util.Inl (_59_1581), _59_1584)::(FStar_Util.Inr (e), _59_1578)::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpat_lid) -> begin
(FStar_Absyn_Syntax.varg e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _59_1599); FStar_Absyn_Syntax.tk = _59_1596; FStar_Absyn_Syntax.pos = _59_1594; FStar_Absyn_Syntax.fvs = _59_1592; FStar_Absyn_Syntax.uvs = _59_1590}, (FStar_Util.Inl (t), _59_1606)::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatT_lid) -> begin
(FStar_Absyn_Syntax.targ t)
end
| _59_1612 -> begin
(FStar_All.failwith "Unexpected pattern term")
end))
in (let lemma_pats = (fun p -> (let elts = (list_elements p)
in (match (elts) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _59_1634); FStar_Absyn_Syntax.tk = _59_1631; FStar_Absyn_Syntax.pos = _59_1629; FStar_Absyn_Syntax.fvs = _59_1627; FStar_Absyn_Syntax.uvs = _59_1625}, (FStar_Util.Inr (e), _59_1641)::[]); FStar_Absyn_Syntax.tk = _59_1623; FStar_Absyn_Syntax.pos = _59_1621; FStar_Absyn_Syntax.fvs = _59_1619; FStar_Absyn_Syntax.uvs = _59_1617}::[] when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatOr_lid) -> begin
(let _162_888 = (list_elements e)
in (FStar_All.pipe_right _162_888 (FStar_List.map (fun branch -> (let _162_887 = (list_elements branch)
in (FStar_All.pipe_right _162_887 (FStar_List.map v_or_t_pat)))))))
end
| _59_1650 -> begin
(let _162_889 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_162_889)::[])
end)))
in (let _59_1693 = (match ((let _162_890 = (FStar_Absyn_Util.compress_typ t)
in _162_890.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (ct); FStar_Absyn_Syntax.tk = _59_1659; FStar_Absyn_Syntax.pos = _59_1657; FStar_Absyn_Syntax.fvs = _59_1655; FStar_Absyn_Syntax.uvs = _59_1653}) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (pre), _59_1678)::(FStar_Util.Inl (post), _59_1673)::(FStar_Util.Inr (pats), _59_1668)::[] -> begin
(let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _162_891 = (lemma_pats pats')
in (binders, pre, post, _162_891)))
end
| _59_1686 -> begin
(FStar_All.failwith "impos")
end)
end
| _59_1688 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_59_1693) with
| (binders, pre, post, patterns) -> begin
(let _59_1700 = (encode_binders None binders env)
in (match (_59_1700) with
| (vars, guards, env, decls, _59_1699) -> begin
(let _59_1720 = (let _162_895 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (let _59_1717 = (let _162_894 = (FStar_All.pipe_right branch (FStar_List.map (fun _59_12 -> (match (_59_12) with
| (FStar_Util.Inl (t), _59_1706) -> begin
(encode_formula t env)
end
| (FStar_Util.Inr (e), _59_1711) -> begin
(encode_exp e (let _59_1713 = env
in {bindings = _59_1713.bindings; depth = _59_1713.depth; tcenv = _59_1713.tcenv; warn = _59_1713.warn; cache = _59_1713.cache; nolabels = _59_1713.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _59_1713.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _162_894 FStar_List.unzip))
in (match (_59_1717) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _162_895 FStar_List.unzip))
in (match (_59_1720) with
| (pats, decls') -> begin
(let decls' = (FStar_List.flatten decls')
in (let pats = (match (induction_on) with
| None -> begin
pats
end
| Some (e) -> begin
(match (vars) with
| [] -> begin
pats
end
| l::[] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _162_898 = (let _162_897 = (FStar_ToSMT_Term.mkFreeV l)
in (FStar_ToSMT_Term.mk_Precedes _162_897 e))
in (_162_898)::p))))
end
| _59_1730 -> begin
(let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _162_904 = (FStar_ToSMT_Term.mk_Precedes tl e)
in (_162_904)::p))))
end
| (x, FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _162_906 = (let _162_905 = (FStar_ToSMT_Term.mkFreeV (x, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_LexCons _162_905 tl))
in (aux _162_906 vars))
end
| _59_1742 -> begin
pats
end))
in (let _162_907 = (FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", FStar_ToSMT_Term.Term_sort))
in (aux _162_907 vars)))
end)
end)
in (let env = (let _59_1744 = env
in {bindings = _59_1744.bindings; depth = _59_1744.depth; tcenv = _59_1744.tcenv; warn = _59_1744.warn; cache = _59_1744.cache; nolabels = true; use_zfuel_name = _59_1744.use_zfuel_name; encode_non_total_function_typ = _59_1744.encode_non_total_function_typ})
in (let _59_1749 = (let _162_908 = (FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _162_908 env))
in (match (_59_1749) with
| (pre, decls'') -> begin
(let _59_1752 = (let _162_909 = (FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _162_909 env))
in (match (_59_1752) with
| (post, decls''') -> begin
(let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _162_914 = (let _162_913 = (let _162_912 = (let _162_911 = (let _162_910 = (FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_162_910, post))
in (FStar_ToSMT_Term.mkImp _162_911))
in (pats, vars, _162_912))
in (FStar_ToSMT_Term.mkForall _162_913))
in (_162_914, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula_with_labels : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * labels * FStar_ToSMT_Term.decls_t) = (fun phi env -> (let enc = (fun f l -> (let _59_1773 = (FStar_Util.fold_map (fun decls x -> (match ((Prims.fst x)) with
| FStar_Util.Inl (t) -> begin
(let _59_1765 = (encode_typ_term t env)
in (match (_59_1765) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))
end
| FStar_Util.Inr (e) -> begin
(let _59_1770 = (encode_exp e env)
in (match (_59_1770) with
| (e, decls') -> begin
((FStar_List.append decls decls'), e)
end))
end)) [] l)
in (match (_59_1773) with
| (decls, args) -> begin
(let _162_932 = (f args)
in (_162_932, [], decls))
end)))
in (let enc_prop_c = (fun f l -> (let _59_1793 = (FStar_List.fold_right (fun t _59_1781 -> (match (_59_1781) with
| (phis, labs, decls) -> begin
(match ((Prims.fst t)) with
| FStar_Util.Inl (t) -> begin
(let _59_1787 = (encode_formula_with_labels t env)
in (match (_59_1787) with
| (phi, labs', decls') -> begin
((phi)::phis, (FStar_List.append labs' labs), (FStar_List.append decls' decls))
end))
end
| _59_1789 -> begin
(FStar_All.failwith "Expected a formula")
end)
end)) l ([], [], []))
in (match (_59_1793) with
| (phis, labs, decls) -> begin
(let _162_948 = (f phis)
in (_162_948, labs, decls))
end)))
in (let const_op = (fun f _59_1796 -> (f, [], []))
in (let un_op = (fun f l -> (let _162_962 = (FStar_List.hd l)
in (FStar_All.pipe_left f _162_962)))
in (let bin_op = (fun f _59_13 -> (match (_59_13) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _59_1807 -> begin
(FStar_All.failwith "Impossible")
end))
in (let eq_op = (fun _59_14 -> (match (_59_14) with
| _59_1815::_59_1813::e1::e2::[] -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) l)
end))
in (let mk_imp = (fun _59_15 -> (match (_59_15) with
| (FStar_Util.Inl (lhs), _59_1828)::(FStar_Util.Inl (rhs), _59_1823)::[] -> begin
(let _59_1834 = (encode_formula_with_labels rhs env)
in (match (_59_1834) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _59_1837) -> begin
(l1, labs1, decls1)
end
| _59_1841 -> begin
(let _59_1845 = (encode_formula_with_labels lhs env)
in (match (_59_1845) with
| (l2, labs2, decls2) -> begin
(let _162_976 = (FStar_ToSMT_Term.mkImp (l2, l1))
in (_162_976, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _59_1847 -> begin
(FStar_All.failwith "impossible")
end))
in (let mk_ite = (fun _59_16 -> (match (_59_16) with
| (FStar_Util.Inl (guard), _59_1863)::(FStar_Util.Inl (_then), _59_1858)::(FStar_Util.Inl (_else), _59_1853)::[] -> begin
(let _59_1869 = (encode_formula_with_labels guard env)
in (match (_59_1869) with
| (g, labs1, decls1) -> begin
(let _59_1873 = (encode_formula_with_labels _then env)
in (match (_59_1873) with
| (t, labs2, decls2) -> begin
(let _59_1877 = (encode_formula_with_labels _else env)
in (match (_59_1877) with
| (e, labs3, decls3) -> begin
(let res = (FStar_ToSMT_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append labs1 labs2) labs3), (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _59_1880 -> begin
(FStar_All.failwith "impossible")
end))
in (let unboxInt_l = (fun f l -> (let _162_988 = (FStar_List.map FStar_ToSMT_Term.unboxInt l)
in (f _162_988)))
in (let connectives = (let _162_1049 = (let _162_997 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkAnd))
in (FStar_Absyn_Const.and_lid, _162_997))
in (let _162_1048 = (let _162_1047 = (let _162_1003 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkOr))
in (FStar_Absyn_Const.or_lid, _162_1003))
in (let _162_1046 = (let _162_1045 = (let _162_1044 = (let _162_1012 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkIff))
in (FStar_Absyn_Const.iff_lid, _162_1012))
in (let _162_1043 = (let _162_1042 = (let _162_1041 = (let _162_1021 = (FStar_All.pipe_left enc_prop_c (un_op FStar_ToSMT_Term.mkNot))
in (FStar_Absyn_Const.not_lid, _162_1021))
in (let _162_1040 = (let _162_1039 = (let _162_1027 = (FStar_All.pipe_left enc (bin_op FStar_ToSMT_Term.mkEq))
in (FStar_Absyn_Const.eqT_lid, _162_1027))
in (_162_1039)::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op FStar_ToSMT_Term.mkTrue)))::((FStar_Absyn_Const.false_lid, (const_op FStar_ToSMT_Term.mkFalse)))::[])
in (_162_1041)::_162_1040))
in ((FStar_Absyn_Const.ite_lid, mk_ite))::_162_1042)
in (_162_1044)::_162_1043))
in ((FStar_Absyn_Const.imp_lid, mk_imp))::_162_1045)
in (_162_1047)::_162_1046))
in (_162_1049)::_162_1048))
in (let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (phi', msg, r, b)) -> begin
(let _59_1898 = (encode_formula_with_labels phi' env)
in (match (_59_1898) with
| (phi, labs, decls) -> begin
if env.nolabels then begin
(phi, [], decls)
end else begin
(let lvar = (let _162_1052 = (varops.fresh "label")
in (_162_1052, FStar_ToSMT_Term.Bool_sort))
in (let lterm = (FStar_ToSMT_Term.mkFreeV lvar)
in (let lphi = (FStar_ToSMT_Term.mkOr (lterm, phi))
in (lphi, ((lvar, msg, r))::labs, decls))))
end
end))
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _59_1909; FStar_Absyn_Syntax.pos = _59_1907; FStar_Absyn_Syntax.fvs = _59_1905; FStar_Absyn_Syntax.uvs = _59_1903}, _59_1924::(FStar_Util.Inr (l), _59_1921)::(FStar_Util.Inl (phi), _59_1916)::[]) when (FStar_Ident.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_IH) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(let _59_1930 = (encode_exp l env)
in (match (_59_1930) with
| (e, decls) -> begin
(let _59_1933 = (encode_function_type_as_formula (Some (e)) None phi env)
in (match (_59_1933) with
| (f, decls') -> begin
(f, [], (FStar_List.append decls decls'))
end))
end))
end else begin
(FStar_ToSMT_Term.mkTrue, [], [])
end
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _59_1941; FStar_Absyn_Syntax.pos = _59_1939; FStar_Absyn_Syntax.fvs = _59_1937; FStar_Absyn_Syntax.uvs = _59_1935}, _59_1953::(FStar_Util.Inl (phi), _59_1949)::tl) when (FStar_Ident.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_lem) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(let pat = (match (tl) with
| [] -> begin
None
end
| (FStar_Util.Inr (pat), _59_1961)::[] -> begin
Some (pat)
end)
in (let _59_1967 = (encode_function_type_as_formula None pat phi env)
in (match (_59_1967) with
| (f, decls) -> begin
(f, [], decls)
end)))
end else begin
(FStar_ToSMT_Term.mkTrue, [], [])
end
end
| _59_1969 -> begin
(let _59_1972 = (encode_typ_term phi env)
in (match (_59_1972) with
| (tt, decls) -> begin
(let _162_1053 = (FStar_ToSMT_Term.mk_Valid tt)
in (_162_1053, [], decls))
end))
end))
in (let encode_q_body = (fun env bs ps body -> (let _59_1984 = (encode_binders None bs env)
in (match (_59_1984) with
| (vars, guards, env, decls, _59_1983) -> begin
(let _59_2004 = (let _162_1065 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (let _59_2001 = (let _162_1064 = (FStar_All.pipe_right p (FStar_List.map (fun _59_17 -> (match (_59_17) with
| (FStar_Util.Inl (t), _59_1990) -> begin
(encode_typ_term t env)
end
| (FStar_Util.Inr (e), _59_1995) -> begin
(encode_exp e (let _59_1997 = env
in {bindings = _59_1997.bindings; depth = _59_1997.depth; tcenv = _59_1997.tcenv; warn = _59_1997.warn; cache = _59_1997.cache; nolabels = _59_1997.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _59_1997.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _162_1064 FStar_List.unzip))
in (match (_59_2001) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _162_1065 FStar_List.unzip))
in (match (_59_2004) with
| (pats, decls') -> begin
(let _59_2008 = (encode_formula_with_labels body env)
in (match (_59_2008) with
| (body, labs, decls'') -> begin
(let _162_1066 = (FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _162_1066, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (let _59_2009 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _162_1067 = (FStar_Absyn_Print.formula_to_string phi)
in (FStar_Util.print1 ">>>> Destructing as formula ... %s\n" _162_1067))
end else begin
()
end
in (let phi = (FStar_Absyn_Util.compress_typ phi)
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _59_2021 -> (match (_59_2021) with
| (l, _59_2020) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_59_2024, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, pats, body)) -> begin
(let _59_2034 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _162_1084 = (FStar_All.pipe_right vars (FStar_Absyn_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _162_1084))
end else begin
()
end
in (let _59_2042 = (encode_q_body env vars pats body)
in (match (_59_2042) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _162_1087 = (let _162_1086 = (let _162_1085 = (FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _162_1085))
in (FStar_ToSMT_Term.mkForall _162_1086))
in (_162_1087, labs, decls))
end)))
end
| Some (FStar_Absyn_Util.QEx (vars, pats, body)) -> begin
(let _59_2055 = (encode_q_body env vars pats body)
in (match (_59_2055) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _162_1090 = (let _162_1089 = (let _162_1088 = (FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _162_1088))
in (FStar_ToSMT_Term.mkExists _162_1089))
in (_162_1090, labs, decls))
end))
end))))))))))))))))

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}

let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))

let prims : prims_t = (let _59_2061 = (fresh_fvar "a" FStar_ToSMT_Term.Type_sort)
in (match (_59_2061) with
| (asym, a) -> begin
(let _59_2064 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_59_2064) with
| (xsym, x) -> begin
(let _59_2067 = (fresh_fvar "y" FStar_ToSMT_Term.Term_sort)
in (match (_59_2067) with
| (ysym, y) -> begin
(let deffun = (fun vars body x -> (FStar_ToSMT_Term.DefineFun ((x, vars, FStar_ToSMT_Term.Term_sort, body, None)))::[])
in (let quant = (fun vars body x -> (let t1 = (let _162_1133 = (let _162_1132 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (x, _162_1132))
in (FStar_ToSMT_Term.mkApp _162_1133))
in (let vname_decl = (let _162_1135 = (let _162_1134 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _162_1134, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_162_1135))
in (let _162_1141 = (let _162_1140 = (let _162_1139 = (let _162_1138 = (let _162_1137 = (let _162_1136 = (FStar_ToSMT_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _162_1136))
in (FStar_ToSMT_Term.mkForall _162_1137))
in (_162_1138, None))
in FStar_ToSMT_Term.Assume (_162_1139))
in (_162_1140)::[])
in (vname_decl)::_162_1141))))
in (let axy = ((asym, FStar_ToSMT_Term.Type_sort))::((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, FStar_ToSMT_Term.Term_sort))::[]
in (let prims = (let _162_1301 = (let _162_1150 = (let _162_1149 = (let _162_1148 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _162_1148))
in (quant axy _162_1149))
in (FStar_Absyn_Const.op_Eq, _162_1150))
in (let _162_1300 = (let _162_1299 = (let _162_1157 = (let _162_1156 = (let _162_1155 = (let _162_1154 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_ToSMT_Term.mkNot _162_1154))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _162_1155))
in (quant axy _162_1156))
in (FStar_Absyn_Const.op_notEq, _162_1157))
in (let _162_1298 = (let _162_1297 = (let _162_1166 = (let _162_1165 = (let _162_1164 = (let _162_1163 = (let _162_1162 = (FStar_ToSMT_Term.unboxInt x)
in (let _162_1161 = (FStar_ToSMT_Term.unboxInt y)
in (_162_1162, _162_1161)))
in (FStar_ToSMT_Term.mkLT _162_1163))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _162_1164))
in (quant xy _162_1165))
in (FStar_Absyn_Const.op_LT, _162_1166))
in (let _162_1296 = (let _162_1295 = (let _162_1175 = (let _162_1174 = (let _162_1173 = (let _162_1172 = (let _162_1171 = (FStar_ToSMT_Term.unboxInt x)
in (let _162_1170 = (FStar_ToSMT_Term.unboxInt y)
in (_162_1171, _162_1170)))
in (FStar_ToSMT_Term.mkLTE _162_1172))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _162_1173))
in (quant xy _162_1174))
in (FStar_Absyn_Const.op_LTE, _162_1175))
in (let _162_1294 = (let _162_1293 = (let _162_1184 = (let _162_1183 = (let _162_1182 = (let _162_1181 = (let _162_1180 = (FStar_ToSMT_Term.unboxInt x)
in (let _162_1179 = (FStar_ToSMT_Term.unboxInt y)
in (_162_1180, _162_1179)))
in (FStar_ToSMT_Term.mkGT _162_1181))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _162_1182))
in (quant xy _162_1183))
in (FStar_Absyn_Const.op_GT, _162_1184))
in (let _162_1292 = (let _162_1291 = (let _162_1193 = (let _162_1192 = (let _162_1191 = (let _162_1190 = (let _162_1189 = (FStar_ToSMT_Term.unboxInt x)
in (let _162_1188 = (FStar_ToSMT_Term.unboxInt y)
in (_162_1189, _162_1188)))
in (FStar_ToSMT_Term.mkGTE _162_1190))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _162_1191))
in (quant xy _162_1192))
in (FStar_Absyn_Const.op_GTE, _162_1193))
in (let _162_1290 = (let _162_1289 = (let _162_1202 = (let _162_1201 = (let _162_1200 = (let _162_1199 = (let _162_1198 = (FStar_ToSMT_Term.unboxInt x)
in (let _162_1197 = (FStar_ToSMT_Term.unboxInt y)
in (_162_1198, _162_1197)))
in (FStar_ToSMT_Term.mkSub _162_1199))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _162_1200))
in (quant xy _162_1201))
in (FStar_Absyn_Const.op_Subtraction, _162_1202))
in (let _162_1288 = (let _162_1287 = (let _162_1209 = (let _162_1208 = (let _162_1207 = (let _162_1206 = (FStar_ToSMT_Term.unboxInt x)
in (FStar_ToSMT_Term.mkMinus _162_1206))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _162_1207))
in (quant qx _162_1208))
in (FStar_Absyn_Const.op_Minus, _162_1209))
in (let _162_1286 = (let _162_1285 = (let _162_1218 = (let _162_1217 = (let _162_1216 = (let _162_1215 = (let _162_1214 = (FStar_ToSMT_Term.unboxInt x)
in (let _162_1213 = (FStar_ToSMT_Term.unboxInt y)
in (_162_1214, _162_1213)))
in (FStar_ToSMT_Term.mkAdd _162_1215))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _162_1216))
in (quant xy _162_1217))
in (FStar_Absyn_Const.op_Addition, _162_1218))
in (let _162_1284 = (let _162_1283 = (let _162_1227 = (let _162_1226 = (let _162_1225 = (let _162_1224 = (let _162_1223 = (FStar_ToSMT_Term.unboxInt x)
in (let _162_1222 = (FStar_ToSMT_Term.unboxInt y)
in (_162_1223, _162_1222)))
in (FStar_ToSMT_Term.mkMul _162_1224))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _162_1225))
in (quant xy _162_1226))
in (FStar_Absyn_Const.op_Multiply, _162_1227))
in (let _162_1282 = (let _162_1281 = (let _162_1236 = (let _162_1235 = (let _162_1234 = (let _162_1233 = (let _162_1232 = (FStar_ToSMT_Term.unboxInt x)
in (let _162_1231 = (FStar_ToSMT_Term.unboxInt y)
in (_162_1232, _162_1231)))
in (FStar_ToSMT_Term.mkDiv _162_1233))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _162_1234))
in (quant xy _162_1235))
in (FStar_Absyn_Const.op_Division, _162_1236))
in (let _162_1280 = (let _162_1279 = (let _162_1245 = (let _162_1244 = (let _162_1243 = (let _162_1242 = (let _162_1241 = (FStar_ToSMT_Term.unboxInt x)
in (let _162_1240 = (FStar_ToSMT_Term.unboxInt y)
in (_162_1241, _162_1240)))
in (FStar_ToSMT_Term.mkMod _162_1242))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _162_1243))
in (quant xy _162_1244))
in (FStar_Absyn_Const.op_Modulus, _162_1245))
in (let _162_1278 = (let _162_1277 = (let _162_1254 = (let _162_1253 = (let _162_1252 = (let _162_1251 = (let _162_1250 = (FStar_ToSMT_Term.unboxBool x)
in (let _162_1249 = (FStar_ToSMT_Term.unboxBool y)
in (_162_1250, _162_1249)))
in (FStar_ToSMT_Term.mkAnd _162_1251))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _162_1252))
in (quant xy _162_1253))
in (FStar_Absyn_Const.op_And, _162_1254))
in (let _162_1276 = (let _162_1275 = (let _162_1263 = (let _162_1262 = (let _162_1261 = (let _162_1260 = (let _162_1259 = (FStar_ToSMT_Term.unboxBool x)
in (let _162_1258 = (FStar_ToSMT_Term.unboxBool y)
in (_162_1259, _162_1258)))
in (FStar_ToSMT_Term.mkOr _162_1260))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _162_1261))
in (quant xy _162_1262))
in (FStar_Absyn_Const.op_Or, _162_1263))
in (let _162_1274 = (let _162_1273 = (let _162_1270 = (let _162_1269 = (let _162_1268 = (let _162_1267 = (FStar_ToSMT_Term.unboxBool x)
in (FStar_ToSMT_Term.mkNot _162_1267))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _162_1268))
in (quant qx _162_1269))
in (FStar_Absyn_Const.op_Negation, _162_1270))
in (_162_1273)::[])
in (_162_1275)::_162_1274))
in (_162_1277)::_162_1276))
in (_162_1279)::_162_1278))
in (_162_1281)::_162_1280))
in (_162_1283)::_162_1282))
in (_162_1285)::_162_1284))
in (_162_1287)::_162_1286))
in (_162_1289)::_162_1288))
in (_162_1291)::_162_1290))
in (_162_1293)::_162_1292))
in (_162_1295)::_162_1294))
in (_162_1297)::_162_1296))
in (_162_1299)::_162_1298))
in (_162_1301)::_162_1300))
in (let mk = (fun l v -> (let _162_1333 = (FStar_All.pipe_right prims (FStar_List.filter (fun _59_2087 -> (match (_59_2087) with
| (l', _59_2086) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _162_1333 (FStar_List.collect (fun _59_2091 -> (match (_59_2091) with
| (_59_2089, b) -> begin
(b v)
end))))))
in (let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _59_2097 -> (match (_59_2097) with
| (l', _59_2096) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

let primitive_type_axioms : FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.decl Prims.list = (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let yy = ("y", FStar_ToSMT_Term.Term_sort)
in (let y = (FStar_ToSMT_Term.mkFreeV yy)
in (let mk_unit = (fun _59_2103 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let _162_1365 = (let _162_1356 = (let _162_1355 = (FStar_ToSMT_Term.mk_HasType FStar_ToSMT_Term.mk_Term_unit tt)
in (_162_1355, Some ("unit typing")))
in FStar_ToSMT_Term.Assume (_162_1356))
in (let _162_1364 = (let _162_1363 = (let _162_1362 = (let _162_1361 = (let _162_1360 = (let _162_1359 = (let _162_1358 = (let _162_1357 = (FStar_ToSMT_Term.mkEq (x, FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _162_1357))
in (FStar_ToSMT_Term.mkImp _162_1358))
in (((typing_pred)::[])::[], (xx)::[], _162_1359))
in (mkForall_fuel _162_1360))
in (_162_1361, Some ("unit inversion")))
in FStar_ToSMT_Term.Assume (_162_1362))
in (_162_1363)::[])
in (_162_1365)::_162_1364))))
in (let mk_bool = (fun _59_2108 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", FStar_ToSMT_Term.Bool_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _162_1386 = (let _162_1375 = (let _162_1374 = (let _162_1373 = (let _162_1372 = (let _162_1371 = (let _162_1370 = (FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _162_1370))
in (FStar_ToSMT_Term.mkImp _162_1371))
in (((typing_pred)::[])::[], (xx)::[], _162_1372))
in (mkForall_fuel _162_1373))
in (_162_1374, Some ("bool inversion")))
in FStar_ToSMT_Term.Assume (_162_1375))
in (let _162_1385 = (let _162_1384 = (let _162_1383 = (let _162_1382 = (let _162_1381 = (let _162_1380 = (let _162_1377 = (let _162_1376 = (FStar_ToSMT_Term.boxBool b)
in (_162_1376)::[])
in (_162_1377)::[])
in (let _162_1379 = (let _162_1378 = (FStar_ToSMT_Term.boxBool b)
in (FStar_ToSMT_Term.mk_HasType _162_1378 tt))
in (_162_1380, (bb)::[], _162_1379)))
in (FStar_ToSMT_Term.mkForall _162_1381))
in (_162_1382, Some ("bool typing")))
in FStar_ToSMT_Term.Assume (_162_1383))
in (_162_1384)::[])
in (_162_1386)::_162_1385))))))
in (let mk_int = (fun _59_2115 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", FStar_ToSMT_Term.Int_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", FStar_ToSMT_Term.Int_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (let _162_1398 = (let _162_1397 = (let _162_1396 = (let _162_1395 = (let _162_1394 = (let _162_1393 = (FStar_ToSMT_Term.boxInt a)
in (let _162_1392 = (let _162_1391 = (FStar_ToSMT_Term.boxInt b)
in (_162_1391)::[])
in (_162_1393)::_162_1392))
in (tt)::_162_1394)
in (tt)::_162_1395)
in ("Prims.Precedes", _162_1396))
in (FStar_ToSMT_Term.mkApp _162_1397))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _162_1398))
in (let precedes_y_x = (let _162_1399 = (FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _162_1399))
in (let _162_1441 = (let _162_1405 = (let _162_1404 = (let _162_1403 = (let _162_1402 = (let _162_1401 = (let _162_1400 = (FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _162_1400))
in (FStar_ToSMT_Term.mkImp _162_1401))
in (((typing_pred)::[])::[], (xx)::[], _162_1402))
in (mkForall_fuel _162_1403))
in (_162_1404, Some ("int inversion")))
in FStar_ToSMT_Term.Assume (_162_1405))
in (let _162_1440 = (let _162_1439 = (let _162_1413 = (let _162_1412 = (let _162_1411 = (let _162_1410 = (let _162_1407 = (let _162_1406 = (FStar_ToSMT_Term.boxInt b)
in (_162_1406)::[])
in (_162_1407)::[])
in (let _162_1409 = (let _162_1408 = (FStar_ToSMT_Term.boxInt b)
in (FStar_ToSMT_Term.mk_HasType _162_1408 tt))
in (_162_1410, (bb)::[], _162_1409)))
in (FStar_ToSMT_Term.mkForall _162_1411))
in (_162_1412, Some ("int typing")))
in FStar_ToSMT_Term.Assume (_162_1413))
in (let _162_1438 = (let _162_1437 = (let _162_1436 = (let _162_1435 = (let _162_1434 = (let _162_1433 = (let _162_1432 = (let _162_1431 = (let _162_1430 = (let _162_1429 = (let _162_1428 = (let _162_1427 = (let _162_1416 = (let _162_1415 = (FStar_ToSMT_Term.unboxInt x)
in (let _162_1414 = (FStar_ToSMT_Term.mkInteger' 0)
in (_162_1415, _162_1414)))
in (FStar_ToSMT_Term.mkGT _162_1416))
in (let _162_1426 = (let _162_1425 = (let _162_1419 = (let _162_1418 = (FStar_ToSMT_Term.unboxInt y)
in (let _162_1417 = (FStar_ToSMT_Term.mkInteger' 0)
in (_162_1418, _162_1417)))
in (FStar_ToSMT_Term.mkGTE _162_1419))
in (let _162_1424 = (let _162_1423 = (let _162_1422 = (let _162_1421 = (FStar_ToSMT_Term.unboxInt y)
in (let _162_1420 = (FStar_ToSMT_Term.unboxInt x)
in (_162_1421, _162_1420)))
in (FStar_ToSMT_Term.mkLT _162_1422))
in (_162_1423)::[])
in (_162_1425)::_162_1424))
in (_162_1427)::_162_1426))
in (typing_pred_y)::_162_1428)
in (typing_pred)::_162_1429)
in (FStar_ToSMT_Term.mk_and_l _162_1430))
in (_162_1431, precedes_y_x))
in (FStar_ToSMT_Term.mkImp _162_1432))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _162_1433))
in (mkForall_fuel _162_1434))
in (_162_1435, Some ("well-founded ordering on nat (alt)")))
in FStar_ToSMT_Term.Assume (_162_1436))
in (_162_1437)::[])
in (_162_1439)::_162_1438))
in (_162_1441)::_162_1440)))))))))))
in (let mk_int_alias = (fun _59_2127 tt -> (let _162_1450 = (let _162_1449 = (let _162_1448 = (let _162_1447 = (let _162_1446 = (FStar_ToSMT_Term.mkApp (FStar_Absyn_Const.int_lid.FStar_Ident.str, []))
in (tt, _162_1446))
in (FStar_ToSMT_Term.mkEq _162_1447))
in (_162_1448, Some ("mapping to int; for now")))
in FStar_ToSMT_Term.Assume (_162_1449))
in (_162_1450)::[]))
in (let mk_str = (fun _59_2131 tt -> (let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", FStar_ToSMT_Term.String_sort)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _162_1471 = (let _162_1460 = (let _162_1459 = (let _162_1458 = (let _162_1457 = (let _162_1456 = (let _162_1455 = (FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _162_1455))
in (FStar_ToSMT_Term.mkImp _162_1456))
in (((typing_pred)::[])::[], (xx)::[], _162_1457))
in (mkForall_fuel _162_1458))
in (_162_1459, Some ("string inversion")))
in FStar_ToSMT_Term.Assume (_162_1460))
in (let _162_1470 = (let _162_1469 = (let _162_1468 = (let _162_1467 = (let _162_1466 = (let _162_1465 = (let _162_1462 = (let _162_1461 = (FStar_ToSMT_Term.boxString b)
in (_162_1461)::[])
in (_162_1462)::[])
in (let _162_1464 = (let _162_1463 = (FStar_ToSMT_Term.boxString b)
in (FStar_ToSMT_Term.mk_HasType _162_1463 tt))
in (_162_1465, (bb)::[], _162_1464)))
in (FStar_ToSMT_Term.mkForall _162_1466))
in (_162_1467, Some ("string typing")))
in FStar_ToSMT_Term.Assume (_162_1468))
in (_162_1469)::[])
in (_162_1471)::_162_1470))))))
in (let mk_ref = (fun reft_name _59_2139 -> (let r = ("r", FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let refa = (let _162_1478 = (let _162_1477 = (let _162_1476 = (FStar_ToSMT_Term.mkFreeV aa)
in (_162_1476)::[])
in (reft_name, _162_1477))
in (FStar_ToSMT_Term.mkApp _162_1478))
in (let refb = (let _162_1481 = (let _162_1480 = (let _162_1479 = (FStar_ToSMT_Term.mkFreeV bb)
in (_162_1479)::[])
in (reft_name, _162_1480))
in (FStar_ToSMT_Term.mkApp _162_1481))
in (let typing_pred = (FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (FStar_ToSMT_Term.mk_HasType x refb)
in (let _162_1500 = (let _162_1487 = (let _162_1486 = (let _162_1485 = (let _162_1484 = (let _162_1483 = (let _162_1482 = (FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _162_1482))
in (FStar_ToSMT_Term.mkImp _162_1483))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _162_1484))
in (mkForall_fuel _162_1485))
in (_162_1486, Some ("ref inversion")))
in FStar_ToSMT_Term.Assume (_162_1487))
in (let _162_1499 = (let _162_1498 = (let _162_1497 = (let _162_1496 = (let _162_1495 = (let _162_1494 = (let _162_1493 = (let _162_1492 = (FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _162_1491 = (let _162_1490 = (let _162_1489 = (FStar_ToSMT_Term.mkFreeV aa)
in (let _162_1488 = (FStar_ToSMT_Term.mkFreeV bb)
in (_162_1489, _162_1488)))
in (FStar_ToSMT_Term.mkEq _162_1490))
in (_162_1492, _162_1491)))
in (FStar_ToSMT_Term.mkImp _162_1493))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _162_1494))
in (mkForall_fuel' 2 _162_1495))
in (_162_1496, Some ("ref typing is injective")))
in FStar_ToSMT_Term.Assume (_162_1497))
in (_162_1498)::[])
in (_162_1500)::_162_1499))))))))))
in (let mk_false_interp = (fun _59_2149 false_tm -> (let valid = (FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _162_1507 = (let _162_1506 = (let _162_1505 = (FStar_ToSMT_Term.mkIff (FStar_ToSMT_Term.mkFalse, valid))
in (_162_1505, Some ("False interpretation")))
in FStar_ToSMT_Term.Assume (_162_1506))
in (_162_1507)::[])))
in (let mk_and_interp = (fun conj _59_2155 -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _162_1514 = (let _162_1513 = (let _162_1512 = (FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_162_1512)::[])
in ("Valid", _162_1513))
in (FStar_ToSMT_Term.mkApp _162_1514))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _162_1521 = (let _162_1520 = (let _162_1519 = (let _162_1518 = (let _162_1517 = (let _162_1516 = (let _162_1515 = (FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_162_1515, valid))
in (FStar_ToSMT_Term.mkIff _162_1516))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1517))
in (FStar_ToSMT_Term.mkForall _162_1518))
in (_162_1519, Some ("/\\ interpretation")))
in FStar_ToSMT_Term.Assume (_162_1520))
in (_162_1521)::[])))))))))
in (let mk_or_interp = (fun disj _59_2166 -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _162_1528 = (let _162_1527 = (let _162_1526 = (FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_162_1526)::[])
in ("Valid", _162_1527))
in (FStar_ToSMT_Term.mkApp _162_1528))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _162_1535 = (let _162_1534 = (let _162_1533 = (let _162_1532 = (let _162_1531 = (let _162_1530 = (let _162_1529 = (FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_162_1529, valid))
in (FStar_ToSMT_Term.mkIff _162_1530))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1531))
in (FStar_ToSMT_Term.mkForall _162_1532))
in (_162_1533, Some ("\\/ interpretation")))
in FStar_ToSMT_Term.Assume (_162_1534))
in (_162_1535)::[])))))))))
in (let mk_eq2_interp = (fun eq2 tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let yy = ("y", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let y = (FStar_ToSMT_Term.mkFreeV yy)
in (let valid = (let _162_1542 = (let _162_1541 = (let _162_1540 = (FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_162_1540)::[])
in ("Valid", _162_1541))
in (FStar_ToSMT_Term.mkApp _162_1542))
in (let _162_1549 = (let _162_1548 = (let _162_1547 = (let _162_1546 = (let _162_1545 = (let _162_1544 = (let _162_1543 = (FStar_ToSMT_Term.mkEq (x, y))
in (_162_1543, valid))
in (FStar_ToSMT_Term.mkIff _162_1544))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _162_1545))
in (FStar_ToSMT_Term.mkForall _162_1546))
in (_162_1547, Some ("Eq2 interpretation")))
in FStar_ToSMT_Term.Assume (_162_1548))
in (_162_1549)::[])))))))))))
in (let mk_imp_interp = (fun imp tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _162_1556 = (let _162_1555 = (let _162_1554 = (FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_162_1554)::[])
in ("Valid", _162_1555))
in (FStar_ToSMT_Term.mkApp _162_1556))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _162_1563 = (let _162_1562 = (let _162_1561 = (let _162_1560 = (let _162_1559 = (let _162_1558 = (let _162_1557 = (FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_162_1557, valid))
in (FStar_ToSMT_Term.mkIff _162_1558))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1559))
in (FStar_ToSMT_Term.mkForall _162_1560))
in (_162_1561, Some ("==> interpretation")))
in FStar_ToSMT_Term.Assume (_162_1562))
in (_162_1563)::[])))))))))
in (let mk_iff_interp = (fun iff tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _162_1570 = (let _162_1569 = (let _162_1568 = (FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_162_1568)::[])
in ("Valid", _162_1569))
in (FStar_ToSMT_Term.mkApp _162_1570))
in (let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _162_1577 = (let _162_1576 = (let _162_1575 = (let _162_1574 = (let _162_1573 = (let _162_1572 = (let _162_1571 = (FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_162_1571, valid))
in (FStar_ToSMT_Term.mkIff _162_1572))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1573))
in (FStar_ToSMT_Term.mkForall _162_1574))
in (_162_1575, Some ("<==> interpretation")))
in FStar_ToSMT_Term.Assume (_162_1576))
in (_162_1577)::[])))))))))
in (let mk_forall_interp = (fun for_all tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _162_1584 = (let _162_1583 = (let _162_1582 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_162_1582)::[])
in ("Valid", _162_1583))
in (FStar_ToSMT_Term.mkApp _162_1584))
in (let valid_b_x = (let _162_1587 = (let _162_1586 = (let _162_1585 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_162_1585)::[])
in ("Valid", _162_1586))
in (FStar_ToSMT_Term.mkApp _162_1587))
in (let _162_1601 = (let _162_1600 = (let _162_1599 = (let _162_1598 = (let _162_1597 = (let _162_1596 = (let _162_1595 = (let _162_1594 = (let _162_1593 = (let _162_1589 = (let _162_1588 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_162_1588)::[])
in (_162_1589)::[])
in (let _162_1592 = (let _162_1591 = (let _162_1590 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_162_1590, valid_b_x))
in (FStar_ToSMT_Term.mkImp _162_1591))
in (_162_1593, (xx)::[], _162_1592)))
in (FStar_ToSMT_Term.mkForall _162_1594))
in (_162_1595, valid))
in (FStar_ToSMT_Term.mkIff _162_1596))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1597))
in (FStar_ToSMT_Term.mkForall _162_1598))
in (_162_1599, Some ("forall interpretation")))
in FStar_ToSMT_Term.Assume (_162_1600))
in (_162_1601)::[]))))))))))
in (let mk_exists_interp = (fun for_all tt -> (let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid = (let _162_1608 = (let _162_1607 = (let _162_1606 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_162_1606)::[])
in ("Valid", _162_1607))
in (FStar_ToSMT_Term.mkApp _162_1608))
in (let valid_b_x = (let _162_1611 = (let _162_1610 = (let _162_1609 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_162_1609)::[])
in ("Valid", _162_1610))
in (FStar_ToSMT_Term.mkApp _162_1611))
in (let _162_1625 = (let _162_1624 = (let _162_1623 = (let _162_1622 = (let _162_1621 = (let _162_1620 = (let _162_1619 = (let _162_1618 = (let _162_1617 = (let _162_1613 = (let _162_1612 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_162_1612)::[])
in (_162_1613)::[])
in (let _162_1616 = (let _162_1615 = (let _162_1614 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_162_1614, valid_b_x))
in (FStar_ToSMT_Term.mkImp _162_1615))
in (_162_1617, (xx)::[], _162_1616)))
in (FStar_ToSMT_Term.mkExists _162_1618))
in (_162_1619, valid))
in (FStar_ToSMT_Term.mkIff _162_1620))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1621))
in (FStar_ToSMT_Term.mkForall _162_1622))
in (_162_1623, Some ("exists interpretation")))
in FStar_ToSMT_Term.Assume (_162_1624))
in (_162_1625)::[]))))))))))
in (let mk_foralltyp_interp = (fun for_all tt -> (let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (let k = (FStar_ToSMT_Term.mkFreeV kk)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _162_1632 = (let _162_1631 = (let _162_1630 = (FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_162_1630)::[])
in ("Valid", _162_1631))
in (FStar_ToSMT_Term.mkApp _162_1632))
in (let valid_a_b = (let _162_1635 = (let _162_1634 = (let _162_1633 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_162_1633)::[])
in ("Valid", _162_1634))
in (FStar_ToSMT_Term.mkApp _162_1635))
in (let _162_1649 = (let _162_1648 = (let _162_1647 = (let _162_1646 = (let _162_1645 = (let _162_1644 = (let _162_1643 = (let _162_1642 = (let _162_1641 = (let _162_1637 = (let _162_1636 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_162_1636)::[])
in (_162_1637)::[])
in (let _162_1640 = (let _162_1639 = (let _162_1638 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_162_1638, valid_a_b))
in (FStar_ToSMT_Term.mkImp _162_1639))
in (_162_1641, (bb)::[], _162_1640)))
in (FStar_ToSMT_Term.mkForall _162_1642))
in (_162_1643, valid))
in (FStar_ToSMT_Term.mkIff _162_1644))
in (((valid)::[])::[], (kk)::(aa)::[], _162_1645))
in (FStar_ToSMT_Term.mkForall _162_1646))
in (_162_1647, Some ("ForallTyp interpretation")))
in FStar_ToSMT_Term.Assume (_162_1648))
in (_162_1649)::[]))))))))))
in (let mk_existstyp_interp = (fun for_some tt -> (let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (let k = (FStar_ToSMT_Term.mkFreeV kk)
in (let a = (FStar_ToSMT_Term.mkFreeV aa)
in (let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let valid = (let _162_1656 = (let _162_1655 = (let _162_1654 = (FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_162_1654)::[])
in ("Valid", _162_1655))
in (FStar_ToSMT_Term.mkApp _162_1656))
in (let valid_a_b = (let _162_1659 = (let _162_1658 = (let _162_1657 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_162_1657)::[])
in ("Valid", _162_1658))
in (FStar_ToSMT_Term.mkApp _162_1659))
in (let _162_1673 = (let _162_1672 = (let _162_1671 = (let _162_1670 = (let _162_1669 = (let _162_1668 = (let _162_1667 = (let _162_1666 = (let _162_1665 = (let _162_1661 = (let _162_1660 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_162_1660)::[])
in (_162_1661)::[])
in (let _162_1664 = (let _162_1663 = (let _162_1662 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_162_1662, valid_a_b))
in (FStar_ToSMT_Term.mkImp _162_1663))
in (_162_1665, (bb)::[], _162_1664)))
in (FStar_ToSMT_Term.mkExists _162_1666))
in (_162_1667, valid))
in (FStar_ToSMT_Term.mkIff _162_1668))
in (((valid)::[])::[], (kk)::(aa)::[], _162_1669))
in (FStar_ToSMT_Term.mkForall _162_1670))
in (_162_1671, Some ("ExistsTyp interpretation")))
in FStar_ToSMT_Term.Assume (_162_1672))
in (_162_1673)::[]))))))))))
in (let prims = ((FStar_Absyn_Const.unit_lid, mk_unit))::((FStar_Absyn_Const.bool_lid, mk_bool))::((FStar_Absyn_Const.int_lid, mk_int))::((FStar_Absyn_Const.string_lid, mk_str))::((FStar_Absyn_Const.ref_lid, mk_ref))::((FStar_Absyn_Const.char_lid, mk_int_alias))::((FStar_Absyn_Const.uint8_lid, mk_int_alias))::((FStar_Absyn_Const.false_lid, mk_false_interp))::((FStar_Absyn_Const.and_lid, mk_and_interp))::((FStar_Absyn_Const.or_lid, mk_or_interp))::((FStar_Absyn_Const.eq2_lid, mk_eq2_interp))::((FStar_Absyn_Const.imp_lid, mk_imp_interp))::((FStar_Absyn_Const.iff_lid, mk_iff_interp))::((FStar_Absyn_Const.forall_lid, mk_forall_interp))::((FStar_Absyn_Const.exists_lid, mk_exists_interp))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _59_2259 -> (match (_59_2259) with
| (l, _59_2258) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_59_2262, f) -> begin
(f s tt)
end)))))))))))))))))))))))

let rec encode_sigelt : env_t  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_ToSMT_Term.decls_t * env_t) = (fun env se -> (let _59_2268 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _162_1816 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _162_1816))
end else begin
()
end
in (let nm = (match ((FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (let _59_2276 = (encode_sigelt' env se)
in (match (_59_2276) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _162_1819 = (let _162_1818 = (let _162_1817 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_ToSMT_Term.Caption (_162_1817))
in (_162_1818)::[])
in (_162_1819, e))
end
| _59_2279 -> begin
(let _162_1826 = (let _162_1825 = (let _162_1821 = (let _162_1820 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_162_1820))
in (_162_1821)::g)
in (let _162_1824 = (let _162_1823 = (let _162_1822 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_162_1822))
in (_162_1823)::[])
in (FStar_List.append _162_1825 _162_1824)))
in (_162_1826, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_ToSMT_Term.decls_t * env_t) = (fun env se -> (let should_skip = (fun l -> ((((FStar_Util.starts_with l.FStar_Ident.str "Prims.pure_") || (FStar_Util.starts_with l.FStar_Ident.str "Prims.ex_")) || (FStar_Util.starts_with l.FStar_Ident.str "Prims.st_")) || (FStar_Util.starts_with l.FStar_Ident.str "Prims.all_")))
in (let encode_top_level_val = (fun env lid t quals -> (let tt = (whnf env t)
in (let _59_2292 = (encode_free_var env lid t tt quals)
in (match (_59_2292) with
| (decls, env) -> begin
if (FStar_Absyn_Util.is_smt_lemma t) then begin
(let _162_1840 = (let _162_1839 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _162_1839))
in (_162_1840, env))
end else begin
(decls, env)
end
end))))
in (let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _59_2299 lb -> (match (_59_2299) with
| (decls, env) -> begin
(let _59_2303 = (let _162_1849 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (encode_top_level_val env _162_1849 lb.FStar_Absyn_Syntax.lbtyp quals))
in (match (_59_2303) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_59_2305, _59_2307, _59_2309, _59_2311, FStar_Absyn_Syntax.Effect::[], _59_2315) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _59_2320, _59_2322, _59_2324, _59_2326, _59_2328) when (should_skip lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _59_2333, _59_2335, _59_2337, _59_2339, _59_2341) when (FStar_Ident.lid_equals lid FStar_Absyn_Const.b2t_lid) -> begin
(let _59_2347 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_59_2347) with
| (tname, ttok, env) -> begin
(let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (let x = (FStar_ToSMT_Term.mkFreeV xx)
in (let valid_b2t_x = (let _162_1852 = (let _162_1851 = (let _162_1850 = (FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (_162_1850)::[])
in ("Valid", _162_1851))
in (FStar_ToSMT_Term.mkApp _162_1852))
in (let decls = (let _162_1860 = (let _162_1859 = (let _162_1858 = (let _162_1857 = (let _162_1856 = (let _162_1855 = (let _162_1854 = (let _162_1853 = (FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _162_1853))
in (FStar_ToSMT_Term.mkEq _162_1854))
in (((valid_b2t_x)::[])::[], (xx)::[], _162_1855))
in (FStar_ToSMT_Term.mkForall _162_1856))
in (_162_1857, Some ("b2t def")))
in FStar_ToSMT_Term.Assume (_162_1858))
in (_162_1859)::[])
in (FStar_ToSMT_Term.DeclFun ((tname, (FStar_ToSMT_Term.Term_sort)::[], FStar_ToSMT_Term.Type_sort, None)))::_162_1860)
in (decls, env)))))
end))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _59_2355, t, tags, _59_2359) -> begin
(let _59_2365 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_59_2365) with
| (tname, ttok, env) -> begin
(let _59_2374 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (tps', body) -> begin
((FStar_List.append tps tps'), body)
end
| _59_2371 -> begin
(tps, t)
end)
in (match (_59_2374) with
| (tps, t) -> begin
(let _59_2381 = (encode_binders None tps env)
in (match (_59_2381) with
| (vars, guards, env', binder_decls, _59_2380) -> begin
(let tok_app = (let _162_1861 = (FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _162_1861 vars))
in (let tok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, None))
in (let app = (let _162_1863 = (let _162_1862 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _162_1862))
in (FStar_ToSMT_Term.mkApp _162_1863))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _59_2387 -> begin
(let _162_1865 = (let _162_1864 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _162_1864))
in (_162_1865)::[])
end)
in (let decls = (let _162_1876 = (let _162_1869 = (let _162_1868 = (let _162_1867 = (let _162_1866 = (FStar_List.map Prims.snd vars)
in (tname, _162_1866, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_162_1867))
in (_162_1868)::(tok_decl)::[])
in (FStar_List.append _162_1869 fresh_tok))
in (let _162_1875 = (let _162_1874 = (let _162_1873 = (let _162_1872 = (let _162_1871 = (let _162_1870 = (FStar_ToSMT_Term.mkEq (tok_app, app))
in (((tok_app)::[])::[], vars, _162_1870))
in (FStar_ToSMT_Term.mkForall _162_1871))
in (_162_1872, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_162_1873))
in (_162_1874)::[])
in (FStar_List.append _162_1876 _162_1875)))
in (let t = if (FStar_All.pipe_right tags (FStar_List.contains FStar_Absyn_Syntax.Opaque)) then begin
(FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
end else begin
(whnf env t)
end
in (let _59_2399 = if (FStar_All.pipe_right tags (FStar_Util.for_some (fun _59_18 -> (match (_59_18) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _59_2394 -> begin
false
end)))) then begin
(let _162_1879 = (FStar_ToSMT_Term.mk_Valid app)
in (let _162_1878 = (encode_formula t env')
in (_162_1879, _162_1878)))
end else begin
(let _162_1880 = (encode_typ_term t env')
in (app, _162_1880))
end
in (match (_59_2399) with
| (def, (body, decls1)) -> begin
(let abbrev_def = (let _162_1887 = (let _162_1886 = (let _162_1885 = (let _162_1884 = (let _162_1883 = (let _162_1882 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _162_1881 = (FStar_ToSMT_Term.mkEq (def, body))
in (_162_1882, _162_1881)))
in (FStar_ToSMT_Term.mkImp _162_1883))
in (((def)::[])::[], vars, _162_1884))
in (FStar_ToSMT_Term.mkForall _162_1885))
in (_162_1886, Some ("abbrev. elimination")))
in FStar_ToSMT_Term.Assume (_162_1887))
in (let kindingAx = (let _59_2403 = (let _162_1888 = (FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _162_1888 env' app))
in (match (_59_2403) with
| (k, decls) -> begin
(let _162_1896 = (let _162_1895 = (let _162_1894 = (let _162_1893 = (let _162_1892 = (let _162_1891 = (let _162_1890 = (let _162_1889 = (FStar_ToSMT_Term.mk_and_l guards)
in (_162_1889, k))
in (FStar_ToSMT_Term.mkImp _162_1890))
in (((app)::[])::[], vars, _162_1891))
in (FStar_ToSMT_Term.mkForall _162_1892))
in (_162_1893, Some ("abbrev. kinding")))
in FStar_ToSMT_Term.Assume (_162_1894))
in (_162_1895)::[])
in (FStar_List.append decls _162_1896))
end))
in (let g = (let _162_1897 = (primitive_type_axioms lid tname app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _162_1897))
in (g, env))))
end))))))))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _59_2410) -> begin
if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || env.tcenv.FStar_Tc_Env.is_iface) then begin
(encode_top_level_val env lid t quals)
end else begin
([], env)
end
end
| FStar_Absyn_Syntax.Sig_assume (l, f, _59_2416, _59_2418) -> begin
(let _59_2423 = (encode_formula f env)
in (match (_59_2423) with
| (f, decls) -> begin
(let g = (let _162_1902 = (let _162_1901 = (let _162_1900 = (let _162_1899 = (let _162_1898 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "Assumption: %s" _162_1898))
in Some (_162_1899))
in (f, _162_1900))
in FStar_ToSMT_Term.Assume (_162_1901))
in (_162_1902)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _59_2429, datas, quals, _59_2433) when (FStar_Ident.lid_equals t FStar_Absyn_Const.precedes_lid) -> begin
(let _59_2439 = (new_typ_constant_and_tok_from_lid env t)
in (match (_59_2439) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, _59_2442, _59_2444, _59_2446, _59_2448, _59_2450, _59_2452) when ((FStar_Ident.lid_equals t FStar_Absyn_Const.char_lid) || (FStar_Ident.lid_equals t FStar_Absyn_Const.uint8_lid)) -> begin
(let tname = t.FStar_Ident.str
in (let tsym = (FStar_ToSMT_Term.mkFreeV (tname, FStar_ToSMT_Term.Type_sort))
in (let decl = FStar_ToSMT_Term.DeclFun ((tname, [], FStar_ToSMT_Term.Type_sort, None))
in (let _162_1904 = (let _162_1903 = (primitive_type_axioms t tname tsym)
in (decl)::_162_1903)
in (_162_1904, (push_free_tvar env t tname (Some (tsym))))))))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _59_2462, datas, quals, _59_2466) -> begin
(let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _59_19 -> (match (_59_19) with
| (FStar_Absyn_Syntax.Logic) | (FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _59_2473 -> begin
false
end))))
in (let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(let _59_2483 = c
in (match (_59_2483) with
| (name, args, _59_2480, _59_2482) -> begin
(let _162_1910 = (let _162_1909 = (let _162_1908 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _162_1908, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_162_1909))
in (_162_1910)::[])
end))
end else begin
(FStar_ToSMT_Term.constructor_to_decl c)
end)
in (let inversion_axioms = (fun tapp vars -> if (((FStar_List.length datas) = 0) || (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _162_1916 = (FStar_Tc_Env.lookup_qname env.tcenv l)
in (FStar_All.pipe_right _162_1916 FStar_Option.isNone)))))) then begin
[]
end else begin
(let _59_2490 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_59_2490) with
| (xxsym, xx) -> begin
(let _59_2533 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _59_2493 l -> (match (_59_2493) with
| (out, decls) -> begin
(let data_t = (FStar_Tc_Env.lookup_datacon env.tcenv l)
in (let _59_2503 = (match ((FStar_Absyn_Util.function_formals data_t)) with
| Some (formals, res) -> begin
(formals, (FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_59_2503) with
| (args, res) -> begin
(let indices = (match ((let _162_1919 = (FStar_Absyn_Util.compress_typ res)
in _162_1919.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (_59_2505, indices) -> begin
indices
end
| _59_2510 -> begin
[]
end)
in (let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (a) -> begin
(let _162_1924 = (let _162_1923 = (let _162_1922 = (mk_typ_projector_name l a.FStar_Absyn_Syntax.v)
in (_162_1922, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _162_1923))
in (push_typ_var env a.FStar_Absyn_Syntax.v _162_1924))
end
| FStar_Util.Inr (x) -> begin
(let _162_1927 = (let _162_1926 = (let _162_1925 = (mk_term_projector_name l x.FStar_Absyn_Syntax.v)
in (_162_1925, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _162_1926))
in (push_term_var env x.FStar_Absyn_Syntax.v _162_1927))
end)) env))
in (let _59_2521 = (encode_args indices env)
in (match (_59_2521) with
| (indices, decls') -> begin
(let _59_2522 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (let eqs = (let _162_1934 = (FStar_List.map2 (fun v a -> (match (a) with
| FStar_Util.Inl (a) -> begin
(let _162_1931 = (let _162_1930 = (FStar_ToSMT_Term.mkFreeV v)
in (_162_1930, a))
in (FStar_ToSMT_Term.mkEq _162_1931))
end
| FStar_Util.Inr (a) -> begin
(let _162_1933 = (let _162_1932 = (FStar_ToSMT_Term.mkFreeV v)
in (_162_1932, a))
in (FStar_ToSMT_Term.mkEq _162_1933))
end)) vars indices)
in (FStar_All.pipe_right _162_1934 FStar_ToSMT_Term.mk_and_l))
in (let _162_1939 = (let _162_1938 = (let _162_1937 = (let _162_1936 = (let _162_1935 = (mk_data_tester env l xx)
in (_162_1935, eqs))
in (FStar_ToSMT_Term.mkAnd _162_1936))
in (out, _162_1937))
in (FStar_ToSMT_Term.mkOr _162_1938))
in (_162_1939, (FStar_List.append decls decls')))))
end))))
end)))
end)) (FStar_ToSMT_Term.mkFalse, [])))
in (match (_59_2533) with
| (data_ax, decls) -> begin
(let _59_2536 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_59_2536) with
| (ffsym, ff) -> begin
(let xx_has_type = (let _162_1940 = (FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_ToSMT_Term.mk_HasTypeFuel _162_1940 xx tapp))
in (let _162_1947 = (let _162_1946 = (let _162_1945 = (let _162_1944 = (let _162_1943 = (let _162_1942 = (add_fuel (ffsym, FStar_ToSMT_Term.Fuel_sort) (((xxsym, FStar_ToSMT_Term.Term_sort))::vars))
in (let _162_1941 = (FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _162_1942, _162_1941)))
in (FStar_ToSMT_Term.mkForall _162_1943))
in (_162_1944, Some ("inversion axiom")))
in FStar_ToSMT_Term.Assume (_162_1945))
in (_162_1946)::[])
in (FStar_List.append decls _162_1947)))
end))
end))
end))
end)
in (let k = (FStar_Absyn_Util.close_kind tps k)
in (let _59_2548 = (match ((let _162_1948 = (FStar_Absyn_Util.compress_kind k)
in _162_1948.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_arrow (bs, res) -> begin
(true, bs, res)
end
| _59_2544 -> begin
(false, [], k)
end)
in (match (_59_2548) with
| (is_kind_arrow, formals, res) -> begin
(let _59_2555 = (encode_binders None formals env)
in (match (_59_2555) with
| (vars, guards, env', binder_decls, _59_2554) -> begin
(let projection_axioms = (fun tapp vars -> (match ((FStar_All.pipe_right quals (FStar_Util.find_opt (fun _59_20 -> (match (_59_20) with
| FStar_Absyn_Syntax.Projector (_59_2561) -> begin
true
end
| _59_2564 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.Projector (d, FStar_Util.Inl (a))) -> begin
(let rec projectee = (fun i _59_21 -> (match (_59_21) with
| [] -> begin
i
end
| f::tl -> begin
(match ((Prims.fst f)) with
| FStar_Util.Inl (_59_2579) -> begin
(projectee (i + 1) tl)
end
| FStar_Util.Inr (x) -> begin
if (x.FStar_Absyn_Syntax.v.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = "projectee") then begin
i
end else begin
(projectee (i + 1) tl)
end
end)
end))
in (let projectee_pos = (projectee 0 formals)
in (let _59_2594 = (match ((FStar_Util.first_N projectee_pos vars)) with
| (_59_2585, xx::suffix) -> begin
(xx, suffix)
end
| _59_2591 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_59_2594) with
| (xx, suffix) -> begin
(let dproj_app = (let _162_1962 = (let _162_1961 = (let _162_1960 = (mk_typ_projector_name d a)
in (let _162_1959 = (let _162_1958 = (FStar_ToSMT_Term.mkFreeV xx)
in (_162_1958)::[])
in (_162_1960, _162_1959)))
in (FStar_ToSMT_Term.mkApp _162_1961))
in (mk_ApplyT _162_1962 suffix))
in (let _162_1967 = (let _162_1966 = (let _162_1965 = (let _162_1964 = (let _162_1963 = (FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in (((tapp)::[])::[], vars, _162_1963))
in (FStar_ToSMT_Term.mkForall _162_1964))
in (_162_1965, Some ("projector axiom")))
in FStar_ToSMT_Term.Assume (_162_1966))
in (_162_1967)::[]))
end))))
end
| _59_2597 -> begin
[]
end))
in (let pretype_axioms = (fun tapp vars -> (let _59_2603 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_59_2603) with
| (xxsym, xx) -> begin
(let _59_2606 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_59_2606) with
| (ffsym, ff) -> begin
(let xx_has_type = (FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _162_1980 = (let _162_1979 = (let _162_1978 = (let _162_1977 = (let _162_1976 = (let _162_1975 = (let _162_1974 = (let _162_1973 = (let _162_1972 = (FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _162_1972))
in (FStar_ToSMT_Term.mkEq _162_1973))
in (xx_has_type, _162_1974))
in (FStar_ToSMT_Term.mkImp _162_1975))
in (((xx_has_type)::[])::[], ((xxsym, FStar_ToSMT_Term.Term_sort))::((ffsym, FStar_ToSMT_Term.Fuel_sort))::vars, _162_1976))
in (FStar_ToSMT_Term.mkForall _162_1977))
in (_162_1978, Some ("pretyping")))
in FStar_ToSMT_Term.Assume (_162_1979))
in (_162_1980)::[]))
end))
end)))
in (let _59_2611 = (new_typ_constant_and_tok_from_lid env t)
in (match (_59_2611) with
| (tname, ttok, env) -> begin
(let ttok_tm = (FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (let _162_1982 = (let _162_1981 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _162_1981))
in (FStar_ToSMT_Term.mkApp _162_1982))
in (let _59_2632 = (let tname_decl = (let _162_1986 = (let _162_1985 = (FStar_All.pipe_right vars (FStar_List.map (fun _59_2617 -> (match (_59_2617) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _162_1984 = (varops.next_id ())
in (tname, _162_1985, FStar_ToSMT_Term.Type_sort, _162_1984)))
in (constructor_or_logic_type_decl _162_1986))
in (let _59_2629 = (match (vars) with
| [] -> begin
(let _162_1990 = (let _162_1989 = (let _162_1988 = (FStar_ToSMT_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _162_1987 -> Some (_162_1987)) _162_1988))
in (push_free_tvar env t tname _162_1989))
in ([], _162_1990))
end
| _59_2621 -> begin
(let ttok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (let _162_1991 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _162_1991))
in (let ttok_app = (mk_ApplyT ttok_tm vars)
in (let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (let name_tok_corr = (let _162_1995 = (let _162_1994 = (let _162_1993 = (let _162_1992 = (FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _162_1992))
in (FStar_ToSMT_Term.mkForall' _162_1993))
in (_162_1994, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_162_1995))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_59_2629) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_59_2632) with
| (decls, env) -> begin
(let kindingAx = (let _59_2635 = (encode_knd res env' tapp)
in (match (_59_2635) with
| (k, decls) -> begin
(let karr = if is_kind_arrow then begin
(let _162_1999 = (let _162_1998 = (let _162_1997 = (let _162_1996 = (FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _162_1996))
in (_162_1997, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_162_1998))
in (_162_1999)::[])
end else begin
[]
end
in (let _162_2005 = (let _162_2004 = (let _162_2003 = (let _162_2002 = (let _162_2001 = (let _162_2000 = (FStar_ToSMT_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _162_2000))
in (FStar_ToSMT_Term.mkForall _162_2001))
in (_162_2002, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_162_2003))
in (_162_2004)::[])
in (FStar_List.append (FStar_List.append decls karr) _162_2005)))
end))
in (let aux = if is_logical then begin
(let _162_2006 = (projection_axioms tapp vars)
in (FStar_List.append kindingAx _162_2006))
end else begin
(let _162_2013 = (let _162_2011 = (let _162_2009 = (let _162_2007 = (primitive_type_axioms t tname tapp)
in (FStar_List.append kindingAx _162_2007))
in (let _162_2008 = (inversion_axioms tapp vars)
in (FStar_List.append _162_2009 _162_2008)))
in (let _162_2010 = (projection_axioms tapp vars)
in (FStar_List.append _162_2011 _162_2010)))
in (let _162_2012 = (pretype_axioms tapp vars)
in (FStar_List.append _162_2013 _162_2012)))
end
in (let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))))
end))
end))))))
end
| FStar_Absyn_Syntax.Sig_datacon (d, _59_2642, _59_2644, _59_2646, _59_2648, _59_2650) when (FStar_Ident.lid_equals d FStar_Absyn_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_datacon (d, t, (_59_2656, tps, _59_2659), quals, _59_2663, drange) -> begin
(let t = (let _162_2015 = (FStar_List.map (fun _59_2670 -> (match (_59_2670) with
| (x, _59_2669) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit))
end)) tps)
in (FStar_Absyn_Util.close_typ _162_2015 t))
in (let _59_2675 = (new_term_constant_and_tok_from_lid env d)
in (match (_59_2675) with
| (ddconstrsym, ddtok, env) -> begin
(let ddtok_tm = (FStar_ToSMT_Term.mkApp (ddtok, []))
in (let _59_2684 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
(f, (FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_59_2684) with
| (formals, t_res) -> begin
(let _59_2687 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_59_2687) with
| (fuel_var, fuel_tm) -> begin
(let s_fuel_tm = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (let _59_2694 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_59_2694) with
| (vars, guards, env', binder_decls, names) -> begin
(let projectors = (FStar_All.pipe_right names (FStar_List.map (fun _59_22 -> (match (_59_22) with
| FStar_Util.Inl (a) -> begin
(let _162_2017 = (mk_typ_projector_name d a)
in (_162_2017, FStar_ToSMT_Term.Type_sort))
end
| FStar_Util.Inr (x) -> begin
(let _162_2018 = (mk_term_projector_name d x)
in (_162_2018, FStar_ToSMT_Term.Term_sort))
end))))
in (let datacons = (let _162_2020 = (let _162_2019 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_ToSMT_Term.Term_sort, _162_2019))
in (FStar_All.pipe_right _162_2020 FStar_ToSMT_Term.constructor_to_decl))
in (let app = (mk_ApplyE ddtok_tm vars)
in (let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let _59_2708 = (encode_typ_pred None t env ddtok_tm)
in (match (_59_2708) with
| (tok_typing, decls3) -> begin
(let _59_2715 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_59_2715) with
| (vars', guards', env'', decls_formals, _59_2714) -> begin
(let _59_2720 = (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars')
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_59_2720) with
| (ty_pred', decls_pred) -> begin
(let guard' = (FStar_ToSMT_Term.mk_and_l guards')
in (let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _59_2724 -> begin
(let _162_2022 = (let _162_2021 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ddtok, FStar_ToSMT_Term.Term_sort) _162_2021))
in (_162_2022)::[])
end)
in (let encode_elim = (fun _59_2727 -> (match (()) with
| () -> begin
(let _59_2730 = (FStar_Absyn_Util.head_and_args t_res)
in (match (_59_2730) with
| (head, args) -> begin
(match ((let _162_2025 = (FStar_Absyn_Util.compress_typ head)
in _162_2025.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _59_2736 = (encode_args args env')
in (match (_59_2736) with
| (encoded_args, arg_decls) -> begin
(let _59_2760 = (FStar_List.fold_left (fun _59_2740 arg -> (match (_59_2740) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| FStar_Util.Inl (targ) -> begin
(let _59_2748 = (let _162_2028 = (FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _162_2028))
in (match (_59_2748) with
| (_59_2745, tv, env) -> begin
(let _162_2030 = (let _162_2029 = (FStar_ToSMT_Term.mkEq (targ, tv))
in (_162_2029)::eqns)
in (env, (tv)::arg_vars, _162_2030))
end))
end
| FStar_Util.Inr (varg) -> begin
(let _59_2755 = (let _162_2031 = (FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _162_2031))
in (match (_59_2755) with
| (_59_2752, xv, env) -> begin
(let _162_2033 = (let _162_2032 = (FStar_ToSMT_Term.mkEq (varg, xv))
in (_162_2032)::eqns)
in (env, (xv)::arg_vars, _162_2033))
end))
end)
end)) (env', [], []) encoded_args)
in (match (_59_2760) with
| (_59_2757, arg_vars, eqns) -> begin
(let arg_vars = (FStar_List.rev arg_vars)
in (let ty = (FStar_ToSMT_Term.mkApp (encoded_head, arg_vars))
in (let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let ty_pred = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (let arg_binders = (FStar_List.map FStar_ToSMT_Term.fv_of_term arg_vars)
in (let typing_inversion = (let _162_2040 = (let _162_2039 = (let _162_2038 = (let _162_2037 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _162_2036 = (let _162_2035 = (let _162_2034 = (FStar_ToSMT_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _162_2034))
in (FStar_ToSMT_Term.mkImp _162_2035))
in (((ty_pred)::[])::[], _162_2037, _162_2036)))
in (FStar_ToSMT_Term.mkForall _162_2038))
in (_162_2039, Some ("data constructor typing elim")))
in FStar_ToSMT_Term.Assume (_162_2040))
in (let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Absyn_Const.lextop_lid) then begin
(let x = (let _162_2041 = (varops.fresh "x")
in (_162_2041, FStar_ToSMT_Term.Term_sort))
in (let xtm = (FStar_ToSMT_Term.mkFreeV x)
in (let _162_2051 = (let _162_2050 = (let _162_2049 = (let _162_2048 = (let _162_2043 = (let _162_2042 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_162_2042)::[])
in (_162_2043)::[])
in (let _162_2047 = (let _162_2046 = (let _162_2045 = (FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _162_2044 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_162_2045, _162_2044)))
in (FStar_ToSMT_Term.mkImp _162_2046))
in (_162_2048, (x)::[], _162_2047)))
in (FStar_ToSMT_Term.mkForall _162_2049))
in (_162_2050, Some ("lextop is top")))
in FStar_ToSMT_Term.Assume (_162_2051))))
end else begin
(let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| (FStar_ToSMT_Term.Type_sort) | (FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| FStar_ToSMT_Term.Term_sort -> begin
(let _162_2054 = (let _162_2053 = (FStar_ToSMT_Term.mkFreeV v)
in (FStar_ToSMT_Term.mk_Precedes _162_2053 dapp))
in (_162_2054)::[])
end
| _59_2775 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _162_2061 = (let _162_2060 = (let _162_2059 = (let _162_2058 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _162_2057 = (let _162_2056 = (let _162_2055 = (FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _162_2055))
in (FStar_ToSMT_Term.mkImp _162_2056))
in (((ty_pred)::[])::[], _162_2058, _162_2057)))
in (FStar_ToSMT_Term.mkForall _162_2059))
in (_162_2060, Some ("subterm ordering")))
in FStar_ToSMT_Term.Assume (_162_2061)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _59_2779 -> begin
(let _59_2780 = (let _162_2064 = (let _162_2063 = (FStar_Absyn_Print.sli d)
in (let _162_2062 = (FStar_Absyn_Print.typ_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _162_2063 _162_2062)))
in (FStar_Tc_Errors.warn drange _162_2064))
in ([], []))
end)
end))
end))
in (let _59_2784 = (encode_elim ())
in (match (_59_2784) with
| (decls2, elim) -> begin
(let g = (let _162_2089 = (let _162_2088 = (let _162_2073 = (let _162_2072 = (let _162_2071 = (let _162_2070 = (let _162_2069 = (let _162_2068 = (let _162_2067 = (let _162_2066 = (let _162_2065 = (FStar_Absyn_Print.sli d)
in (FStar_Util.format1 "data constructor proxy: %s" _162_2065))
in Some (_162_2066))
in (ddtok, [], FStar_ToSMT_Term.Term_sort, _162_2067))
in FStar_ToSMT_Term.DeclFun (_162_2068))
in (_162_2069)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _162_2070))
in (FStar_List.append _162_2071 proxy_fresh))
in (FStar_List.append _162_2072 decls_formals))
in (FStar_List.append _162_2073 decls_pred))
in (let _162_2087 = (let _162_2086 = (let _162_2085 = (let _162_2077 = (let _162_2076 = (let _162_2075 = (let _162_2074 = (FStar_ToSMT_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _162_2074))
in (FStar_ToSMT_Term.mkForall _162_2075))
in (_162_2076, Some ("equality for proxy")))
in FStar_ToSMT_Term.Assume (_162_2077))
in (let _162_2084 = (let _162_2083 = (let _162_2082 = (let _162_2081 = (let _162_2080 = (let _162_2079 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) vars')
in (let _162_2078 = (FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _162_2079, _162_2078)))
in (FStar_ToSMT_Term.mkForall _162_2080))
in (_162_2081, Some ("data constructor typing intro")))
in FStar_ToSMT_Term.Assume (_162_2082))
in (_162_2083)::[])
in (_162_2085)::_162_2084))
in (FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_162_2086)
in (FStar_List.append _162_2088 _162_2087)))
in (FStar_List.append _162_2089 elim))
in ((FStar_List.append datacons g), env))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end)))
end
| FStar_Absyn_Syntax.Sig_bundle (ses, _59_2788, _59_2790, _59_2792) -> begin
(let _59_2797 = (encode_signature env ses)
in (match (_59_2797) with
| (g, env) -> begin
(let _59_2809 = (FStar_All.pipe_right g (FStar_List.partition (fun _59_23 -> (match (_59_23) with
| FStar_ToSMT_Term.Assume (_59_2800, Some ("inversion axiom")) -> begin
false
end
| _59_2806 -> begin
true
end))))
in (match (_59_2809) with
| (g', inversions) -> begin
(let _59_2818 = (FStar_All.pipe_right g' (FStar_List.partition (fun _59_24 -> (match (_59_24) with
| FStar_ToSMT_Term.DeclFun (_59_2812) -> begin
true
end
| _59_2815 -> begin
false
end))))
in (match (_59_2818) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_let (_59_2820, _59_2822, _59_2824, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _59_25 -> (match (_59_25) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _59_2836 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_let ((is_rec, bindings), _59_2841, _59_2843, quals) -> begin
(let eta_expand = (fun binders formals body t -> (let nbinders = (FStar_List.length binders)
in (let _59_2855 = (FStar_Util.first_N nbinders formals)
in (match (_59_2855) with
| (formals, extra_formals) -> begin
(let subst = (FStar_List.map2 (fun formal binder -> (match (((Prims.fst formal), (Prims.fst binder))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _162_2104 = (let _162_2103 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _162_2103))
in FStar_Util.Inl (_162_2104))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _162_2106 = (let _162_2105 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _162_2105))
in FStar_Util.Inr (_162_2106))
end
| _59_2869 -> begin
(FStar_All.failwith "Impossible")
end)) formals binders)
in (let extra_formals = (let _162_2107 = (FStar_Absyn_Util.subst_binders subst extra_formals)
in (FStar_All.pipe_right _162_2107 FStar_Absyn_Util.name_binders))
in (let body = (let _162_2113 = (let _162_2109 = (let _162_2108 = (FStar_Absyn_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _162_2108))
in (body, _162_2109))
in (let _162_2112 = (let _162_2111 = (FStar_Absyn_Util.subst_typ subst t)
in (FStar_All.pipe_left (fun _162_2110 -> Some (_162_2110)) _162_2111))
in (FStar_Absyn_Syntax.mk_Exp_app_flat _162_2113 _162_2112 body.FStar_Absyn_Syntax.pos)))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (let destruct_bound_function = (fun flid t_norm e -> (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_ascribed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (binders, body); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _, _)) | (FStar_Absyn_Syntax.Exp_abs (binders, body)) -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(let nformals = (FStar_List.length formals)
in (let nbinders = (FStar_List.length binders)
in (let tres = (FStar_Absyn_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Absyn_Util.is_total_comp c)) then begin
(let _59_2907 = (FStar_Util.first_N nformals binders)
in (match (_59_2907) with
| (bs0, rest) -> begin
(let tres = (match ((FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tres)
end
| _59_2911 -> begin
(FStar_All.failwith "impossible")
end)
in (let body = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (tres)) body.FStar_Absyn_Syntax.pos)
in (bs0, body, bs0, tres)))
end))
end else begin
if (nformals > nbinders) then begin
(let _59_2916 = (eta_expand binders formals body tres)
in (match (_59_2916) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end
| _59_2918 -> begin
(let _162_2122 = (let _162_2121 = (FStar_Absyn_Print.exp_to_string e)
in (let _162_2120 = (FStar_Absyn_Print.typ_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _162_2121 _162_2120)))
in (FStar_All.failwith _162_2122))
end)
end
| _59_2920 -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(let tres = (FStar_Absyn_Util.comp_result c)
in (let _59_2928 = (eta_expand [] formals e tres)
in (match (_59_2928) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _59_2930 -> begin
([], e, [], t_norm)
end)
end))
in (FStar_All.try_with (fun _59_2932 -> (match (()) with
| () -> begin
if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _59_26 -> (match (_59_26) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _59_2943 -> begin
false
end)))) || (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp))))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(let _59_2962 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _59_2949 lb -> (match (_59_2949) with
| (toks, typs, decls, env) -> begin
(let _59_2951 = if (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (let t_norm = (let _162_2128 = (whnf env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_right _162_2128 FStar_Absyn_Util.compress_typ))
in (let _59_2957 = (let _162_2129 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _162_2129 lb.FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_59_2957) with
| (tok, decl, env) -> begin
(let _162_2132 = (let _162_2131 = (let _162_2130 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (_162_2130, tok))
in (_162_2131)::toks)
in (_162_2132, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_59_2962) with
| (toks, typs, decls, env) -> begin
(let toks = (FStar_List.rev toks)
in (let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _59_27 -> (match (_59_27) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _59_2969 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> ((FStar_Absyn_Util.is_lemma t) || (let _162_2135 = (FStar_Absyn_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _162_2135))))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Absyn_Syntax.lbname = _59_2977; FStar_Absyn_Syntax.lbtyp = _59_2975; FStar_Absyn_Syntax.lbeff = _59_2973; FStar_Absyn_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(let _59_2993 = (destruct_bound_function flid t_norm e)
in (match (_59_2993) with
| (binders, body, formals, tres) -> begin
(let _59_3000 = (encode_binders None binders env)
in (match (_59_3000) with
| (vars, guards, env', binder_decls, _59_2999) -> begin
(let app = (match (vars) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
end
| _59_3003 -> begin
(let _162_2137 = (let _162_2136 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (f, _162_2136))
in (FStar_ToSMT_Term.mkApp _162_2137))
end)
in (let _59_3007 = (encode_exp body env')
in (match (_59_3007) with
| (body, decls2) -> begin
(let eqn = (let _162_2146 = (let _162_2145 = (let _162_2142 = (let _162_2141 = (let _162_2140 = (let _162_2139 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _162_2138 = (FStar_ToSMT_Term.mkEq (app, body))
in (_162_2139, _162_2138)))
in (FStar_ToSMT_Term.mkImp _162_2140))
in (((app)::[])::[], vars, _162_2141))
in (FStar_ToSMT_Term.mkForall _162_2142))
in (let _162_2144 = (let _162_2143 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_162_2143))
in (_162_2145, _162_2144)))
in FStar_ToSMT_Term.Assume (_162_2146))
in ((FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end))
end
| _59_3010 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(let fuel = (let _162_2147 = (varops.fresh "fuel")
in (_162_2147, FStar_ToSMT_Term.Fuel_sort))
in (let fuel_tm = (FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _59_3027 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _59_3016 _59_3021 -> (match ((_59_3016, _59_3021)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (let _162_2152 = (let _162_2151 = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _162_2150 -> Some (_162_2150)) _162_2151))
in (push_free_var env flid gtok _162_2152))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_59_3027) with
| (gtoks, env) -> begin
(let gtoks = (FStar_List.rev gtoks)
in (let encode_one_binding = (fun env0 _59_3036 t_norm _59_3045 -> (match ((_59_3036, _59_3045)) with
| ((flid, f, ftok, g, gtok), {FStar_Absyn_Syntax.lbname = _59_3044; FStar_Absyn_Syntax.lbtyp = _59_3042; FStar_Absyn_Syntax.lbeff = _59_3040; FStar_Absyn_Syntax.lbdef = e}) -> begin
(let _59_3050 = (destruct_bound_function flid t_norm e)
in (match (_59_3050) with
| (binders, body, formals, tres) -> begin
(let _59_3057 = (encode_binders None binders env)
in (match (_59_3057) with
| (vars, guards, env', binder_decls, _59_3056) -> begin
(let decl_g = (let _162_2163 = (let _162_2162 = (let _162_2161 = (FStar_List.map Prims.snd vars)
in (FStar_ToSMT_Term.Fuel_sort)::_162_2161)
in (g, _162_2162, FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_ToSMT_Term.DeclFun (_162_2163))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = FStar_ToSMT_Term.DeclFun ((gtok, [], FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let app = (FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (let _162_2166 = (let _162_2165 = (let _162_2164 = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_162_2164)::vars_tm)
in (g, _162_2165))
in (FStar_ToSMT_Term.mkApp _162_2166))
in (let gmax = (let _162_2169 = (let _162_2168 = (let _162_2167 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_162_2167)::vars_tm)
in (g, _162_2168))
in (FStar_ToSMT_Term.mkApp _162_2169))
in (let _59_3067 = (encode_exp body env')
in (match (_59_3067) with
| (body_tm, decls2) -> begin
(let eqn_g = (let _162_2178 = (let _162_2177 = (let _162_2174 = (let _162_2173 = (let _162_2172 = (let _162_2171 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _162_2170 = (FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_162_2171, _162_2170)))
in (FStar_ToSMT_Term.mkImp _162_2172))
in (((gsapp)::[])::[], (fuel)::vars, _162_2173))
in (FStar_ToSMT_Term.mkForall _162_2174))
in (let _162_2176 = (let _162_2175 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_162_2175))
in (_162_2177, _162_2176)))
in FStar_ToSMT_Term.Assume (_162_2178))
in (let eqn_f = (let _162_2182 = (let _162_2181 = (let _162_2180 = (let _162_2179 = (FStar_ToSMT_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _162_2179))
in (FStar_ToSMT_Term.mkForall _162_2180))
in (_162_2181, Some ("Correspondence of recursive function to instrumented version")))
in FStar_ToSMT_Term.Assume (_162_2182))
in (let eqn_g' = (let _162_2191 = (let _162_2190 = (let _162_2189 = (let _162_2188 = (let _162_2187 = (let _162_2186 = (let _162_2185 = (let _162_2184 = (let _162_2183 = (FStar_ToSMT_Term.n_fuel 0)
in (_162_2183)::vars_tm)
in (g, _162_2184))
in (FStar_ToSMT_Term.mkApp _162_2185))
in (gsapp, _162_2186))
in (FStar_ToSMT_Term.mkEq _162_2187))
in (((gsapp)::[])::[], (fuel)::vars, _162_2188))
in (FStar_ToSMT_Term.mkForall _162_2189))
in (_162_2190, Some ("Fuel irrelevance")))
in FStar_ToSMT_Term.Assume (_162_2191))
in (let _59_3090 = (let _59_3077 = (encode_binders None formals env0)
in (match (_59_3077) with
| (vars, v_guards, env, binder_decls, _59_3076) -> begin
(let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (let _162_2192 = (FStar_ToSMT_Term.mkFreeV (gtok, FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _162_2192 ((fuel)::vars)))
in (let _162_2196 = (let _162_2195 = (let _162_2194 = (let _162_2193 = (FStar_ToSMT_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _162_2193))
in (FStar_ToSMT_Term.mkForall _162_2194))
in (_162_2195, Some ("Fuel token correspondence")))
in FStar_ToSMT_Term.Assume (_162_2196)))
in (let _59_3087 = (let _59_3084 = (encode_typ_pred None tres env gapp)
in (match (_59_3084) with
| (g_typing, d3) -> begin
(let _162_2204 = (let _162_2203 = (let _162_2202 = (let _162_2201 = (let _162_2200 = (let _162_2199 = (let _162_2198 = (let _162_2197 = (FStar_ToSMT_Term.mk_and_l v_guards)
in (_162_2197, g_typing))
in (FStar_ToSMT_Term.mkImp _162_2198))
in (((gapp)::[])::[], (fuel)::vars, _162_2199))
in (FStar_ToSMT_Term.mkForall _162_2200))
in (_162_2201, None))
in FStar_ToSMT_Term.Assume (_162_2202))
in (_162_2203)::[])
in (d3, _162_2204))
end))
in (match (_59_3087) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_59_3090) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (let _59_3106 = (let _162_2207 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _59_3094 _59_3098 -> (match ((_59_3094, _59_3098)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _59_3102 = (encode_one_binding env0 gtok ty bs)
in (match (_59_3102) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _162_2207))
in (match (_59_3106) with
| (decls, eqns, env0) -> begin
(let _59_3115 = (let _162_2209 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _162_2209 (FStar_List.partition (fun _59_28 -> (match (_59_28) with
| FStar_ToSMT_Term.DeclFun (_59_3109) -> begin
true
end
| _59_3112 -> begin
false
end)))))
in (match (_59_3115) with
| (prefix_decls, rest) -> begin
(let eqns = (FStar_List.rev eqns)
in ((FStar_List.append (FStar_List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end
end)))
end))
end
end)) (fun _59_2931 -> (match (_59_2931) with
| Let_rec_unencodeable -> begin
(let msg = (let _162_2212 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname))))
in (FStar_All.pipe_right _162_2212 (FStar_String.concat " and ")))
in (let decl = FStar_ToSMT_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end)))))
and declare_top_level_let : env_t  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((Prims.string * FStar_ToSMT_Term.term Prims.option) * FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (match ((try_lookup_lid env x)) with
| None -> begin
(let _59_3142 = (encode_free_var env x t t_norm [])
in (match (_59_3142) with
| (decls, env) -> begin
(let _59_3147 = (lookup_lid env x)
in (match (_59_3147) with
| (n, x', _59_3146) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _59_3151) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_ToSMT_Term.decl Prims.list = (fun env lid t -> (let _59_3159 = (encode_function_type_as_formula None None t env)
in (match (_59_3159) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_ToSMT_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)))))::[]))
end)))
and encode_free_var : env_t  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.qualifier Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env lid tt t_norm quals -> if ((let _162_2225 = (FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _162_2225)) || (FStar_Absyn_Util.is_lemma t_norm)) then begin
(let _59_3168 = (new_term_constant_and_tok_from_lid env lid)
in (match (_59_3168) with
| (vname, vtok, env) -> begin
(let arg_sorts = (match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _59_3171) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _59_29 -> (match (_59_29) with
| (FStar_Util.Inl (_59_3176), _59_3179) -> begin
FStar_ToSMT_Term.Type_sort
end
| _59_3182 -> begin
FStar_ToSMT_Term.Term_sort
end))))
end
| _59_3184 -> begin
[]
end)
in (let d = FStar_ToSMT_Term.DeclFun ((vname, arg_sorts, FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (let dd = FStar_ToSMT_Term.DeclFun ((vtok, [], FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(let vname = (varops.new_fvar lid)
in (let definition = (prims.mk lid vname)
in (let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (let _59_3201 = (match ((FStar_Absyn_Util.function_formals t_norm)) with
| Some (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _162_2227 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _162_2227))
end else begin
(args, (None, (FStar_Absyn_Util.comp_result comp)))
end
end
| None -> begin
([], (None, t_norm))
end)
in (match (_59_3201) with
| (formals, (pre_opt, res_t)) -> begin
(let _59_3205 = (new_term_constant_and_tok_from_lid env lid)
in (match (_59_3205) with
| (vname, vtok, env) -> begin
(let vtok_tm = (match (formals) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
end
| _59_3208 -> begin
(FStar_ToSMT_Term.mkApp (vtok, []))
end)
in (let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _59_30 -> (match (_59_30) with
| FStar_Absyn_Syntax.Discriminator (d) -> begin
(let _59_3224 = (FStar_Util.prefix vars)
in (match (_59_3224) with
| (_59_3219, (xxsym, _59_3222)) -> begin
(let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (let _162_2244 = (let _162_2243 = (let _162_2242 = (let _162_2241 = (let _162_2240 = (let _162_2239 = (let _162_2238 = (let _162_2237 = (FStar_ToSMT_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _162_2237))
in (vapp, _162_2238))
in (FStar_ToSMT_Term.mkEq _162_2239))
in (((vapp)::[])::[], vars, _162_2240))
in (FStar_ToSMT_Term.mkForall _162_2241))
in (_162_2242, Some ("Discriminator equation")))
in FStar_ToSMT_Term.Assume (_162_2243))
in (_162_2244)::[]))
end))
end
| FStar_Absyn_Syntax.Projector (d, FStar_Util.Inr (f)) -> begin
(let _59_3237 = (FStar_Util.prefix vars)
in (match (_59_3237) with
| (_59_3232, (xxsym, _59_3235)) -> begin
(let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (let prim_app = (let _162_2246 = (let _162_2245 = (mk_term_projector_name d f)
in (_162_2245, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _162_2246))
in (let _162_2251 = (let _162_2250 = (let _162_2249 = (let _162_2248 = (let _162_2247 = (FStar_ToSMT_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _162_2247))
in (FStar_ToSMT_Term.mkForall _162_2248))
in (_162_2249, Some ("Projector equation")))
in FStar_ToSMT_Term.Assume (_162_2250))
in (_162_2251)::[])))
end))
end
| _59_3241 -> begin
[]
end)))))
in (let _59_3248 = (encode_binders None formals env)
in (match (_59_3248) with
| (vars, guards, env', decls1, _59_3247) -> begin
(let _59_3257 = (match (pre_opt) with
| None -> begin
(let _162_2252 = (FStar_ToSMT_Term.mk_and_l guards)
in (_162_2252, decls1))
end
| Some (p) -> begin
(let _59_3254 = (encode_formula p env')
in (match (_59_3254) with
| (g, ds) -> begin
(let _162_2253 = (FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_162_2253, (FStar_List.append decls1 ds)))
end))
end)
in (match (_59_3257) with
| (guard, decls1) -> begin
(let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (let _162_2255 = (let _162_2254 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (vname, _162_2254))
in (FStar_ToSMT_Term.mkApp _162_2255))
in (let _59_3288 = (let vname_decl = (let _162_2258 = (let _162_2257 = (FStar_All.pipe_right formals (FStar_List.map (fun _59_31 -> (match (_59_31) with
| (FStar_Util.Inl (_59_3262), _59_3265) -> begin
FStar_ToSMT_Term.Type_sort
end
| _59_3268 -> begin
FStar_ToSMT_Term.Term_sort
end))))
in (vname, _162_2257, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_162_2258))
in (let _59_3275 = (let env = (let _59_3270 = env
in {bindings = _59_3270.bindings; depth = _59_3270.depth; tcenv = _59_3270.tcenv; warn = _59_3270.warn; cache = _59_3270.cache; nolabels = _59_3270.nolabels; use_zfuel_name = _59_3270.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_typ_pred None tt env vtok_tm)
end else begin
(encode_typ_pred None t_norm env vtok_tm)
end)
in (match (_59_3275) with
| (tok_typing, decls2) -> begin
(let tok_typing = FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in (let _59_3285 = (match (formals) with
| [] -> begin
(let _162_2262 = (let _162_2261 = (let _162_2260 = (FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
in (FStar_All.pipe_left (fun _162_2259 -> Some (_162_2259)) _162_2260))
in (push_free_var env lid vname _162_2261))
in ((FStar_List.append decls2 ((tok_typing)::[])), _162_2262))
end
| _59_3279 -> begin
(let vtok_decl = FStar_ToSMT_Term.DeclFun ((vtok, [], FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (let _162_2263 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (vtok, FStar_ToSMT_Term.Term_sort) _162_2263))
in (let name_tok_corr = (let _162_2267 = (let _162_2266 = (let _162_2265 = (let _162_2264 = (FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _162_2264))
in (FStar_ToSMT_Term.mkForall _162_2265))
in (_162_2266, None))
in FStar_ToSMT_Term.Assume (_162_2267))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_59_3285) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_59_3288) with
| (decls2, env) -> begin
(let _59_3296 = (let res_t = (FStar_Absyn_Util.compress_typ res_t)
in (let _59_3292 = (encode_typ_term res_t env')
in (match (_59_3292) with
| (encoded_res_t, decls) -> begin
(let _162_2268 = (FStar_ToSMT_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _162_2268, decls))
end)))
in (match (_59_3296) with
| (encoded_res_t, ty_pred, decls3) -> begin
(let typingAx = (let _162_2272 = (let _162_2271 = (let _162_2270 = (let _162_2269 = (FStar_ToSMT_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _162_2269))
in (FStar_ToSMT_Term.mkForall _162_2270))
in (_162_2271, Some ("free var typing")))
in FStar_ToSMT_Term.Assume (_162_2272))
in (let g = (let _162_2274 = (let _162_2273 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_162_2273)
in (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) _162_2274))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end
end)
and encode_signature : env_t  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _59_3303 se -> (match (_59_3303) with
| (g, env) -> begin
(let _59_3307 = (encode_sigelt env se)
in (match (_59_3307) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

let encode_env_bindings : env_t  ->  FStar_Tc_Env.binding Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env bindings -> (let encode_binding = (fun b _59_3314 -> (match (_59_3314) with
| (decls, env) -> begin
(match (b) with
| FStar_Tc_Env.Binding_var (x, t0) -> begin
(let _59_3322 = (new_term_constant env x)
in (match (_59_3322) with
| (xxsym, xx, env') -> begin
(let t1 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (let _59_3324 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _162_2289 = (FStar_Absyn_Print.strBvd x)
in (let _162_2288 = (FStar_Absyn_Print.typ_to_string t0)
in (let _162_2287 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _162_2289 _162_2288 _162_2287))))
end else begin
()
end
in (let _59_3328 = (encode_typ_pred None t1 env xx)
in (match (_59_3328) with
| (t, decls') -> begin
(let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _162_2293 = (let _162_2292 = (FStar_Absyn_Print.strBvd x)
in (let _162_2291 = (FStar_Absyn_Print.typ_to_string t0)
in (let _162_2290 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _162_2292 _162_2291 _162_2290))))
in Some (_162_2293))
end else begin
None
end
in (let g = (FStar_List.append (FStar_List.append ((FStar_ToSMT_Term.DeclFun ((xxsym, [], FStar_ToSMT_Term.Term_sort, caption)))::[]) decls') ((FStar_ToSMT_Term.Assume ((t, None)))::[]))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(let _59_3338 = (new_typ_constant env a)
in (match (_59_3338) with
| (aasym, aa, env') -> begin
(let _59_3341 = (encode_knd k env aa)
in (match (_59_3341) with
| (k, decls') -> begin
(let g = (let _162_2299 = (let _162_2298 = (let _162_2297 = (let _162_2296 = (let _162_2295 = (let _162_2294 = (FStar_Absyn_Print.strBvd a)
in Some (_162_2294))
in (aasym, [], FStar_ToSMT_Term.Type_sort, _162_2295))
in FStar_ToSMT_Term.DeclFun (_162_2296))
in (_162_2297)::[])
in (FStar_List.append _162_2298 decls'))
in (FStar_List.append _162_2299 ((FStar_ToSMT_Term.Assume ((k, None)))::[])))
in ((FStar_List.append decls g), env'))
end))
end))
end
| FStar_Tc_Env.Binding_lid (x, t) -> begin
(let t_norm = (whnf env t)
in (let _59_3350 = (encode_free_var env x t t_norm [])
in (match (_59_3350) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end)))
end
| FStar_Tc_Env.Binding_sig (se) -> begin
(let _59_3355 = (encode_sigelt env se)
in (match (_59_3355) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

let encode_labels = (fun labs -> (let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _59_3362 -> (match (_59_3362) with
| (l, _59_3359, _59_3361) -> begin
FStar_ToSMT_Term.DeclFun (((Prims.fst l), [], FStar_ToSMT_Term.Bool_sort, None))
end))))
in (let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _59_3369 -> (match (_59_3369) with
| (l, _59_3366, _59_3368) -> begin
(let _162_2307 = (FStar_All.pipe_left (fun _162_2303 -> FStar_ToSMT_Term.Echo (_162_2303)) (Prims.fst l))
in (let _162_2306 = (let _162_2305 = (let _162_2304 = (FStar_ToSMT_Term.mkFreeV l)
in FStar_ToSMT_Term.Eval (_162_2304))
in (_162_2305)::[])
in (_162_2307)::_162_2306))
end))))
in (prefix, suffix))))

let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

let init_env : FStar_Tc_Env.env  ->  Prims.unit = (fun tcenv -> (let _162_2312 = (let _162_2311 = (let _162_2310 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _162_2310; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_162_2311)::[])
in (FStar_ST.op_Colon_Equals last_env _162_2312)))

let get_env : FStar_Tc_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_59_3375 -> begin
(let _59_3378 = e
in {bindings = _59_3378.bindings; depth = _59_3378.depth; tcenv = tcenv; warn = _59_3378.warn; cache = _59_3378.cache; nolabels = _59_3378.nolabels; use_zfuel_name = _59_3378.use_zfuel_name; encode_non_total_function_typ = _59_3378.encode_non_total_function_typ})
end))

let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _59_3384::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

let push_env : Prims.unit  ->  Prims.unit = (fun _59_3386 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(let refs = (FStar_Util.smap_copy hd.cache)
in (let top = (let _59_3392 = hd
in {bindings = _59_3392.bindings; depth = _59_3392.depth; tcenv = _59_3392.tcenv; warn = _59_3392.warn; cache = refs; nolabels = _59_3392.nolabels; use_zfuel_name = _59_3392.use_zfuel_name; encode_non_total_function_typ = _59_3392.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

let pop_env : Prims.unit  ->  Prims.unit = (fun _59_3395 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _59_3399::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

let mark_env : Prims.unit  ->  Prims.unit = (fun _59_3401 -> (match (()) with
| () -> begin
(push_env ())
end))

let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _59_3402 -> (match (()) with
| () -> begin
(pop_env ())
end))

let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _59_3403 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_59_3406::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _59_3411 -> begin
(FStar_All.failwith "Impossible")
end)
end))

let init : FStar_Tc_Env.env  ->  Prims.unit = (fun tcenv -> (let _59_3413 = (init_env tcenv)
in (let _59_3415 = (FStar_ToSMT_Z3.init ())
in (FStar_ToSMT_Z3.giveZ3 ((FStar_ToSMT_Term.DefPrelude)::[])))))

let push : Prims.string  ->  Prims.unit = (fun msg -> (let _59_3418 = (push_env ())
in (let _59_3420 = (varops.push ())
in (FStar_ToSMT_Z3.push msg))))

let pop : Prims.string  ->  Prims.unit = (fun msg -> (let _59_3423 = (let _162_2333 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _162_2333))
in (let _59_3425 = (varops.pop ())
in (FStar_ToSMT_Z3.pop msg))))

let mark : Prims.string  ->  Prims.unit = (fun msg -> (let _59_3428 = (mark_env ())
in (let _59_3430 = (varops.mark ())
in (FStar_ToSMT_Z3.mark msg))))

let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (let _59_3433 = (reset_mark_env ())
in (let _59_3435 = (varops.reset_mark ())
in (FStar_ToSMT_Z3.reset_mark msg))))

let commit_mark = (fun msg -> (let _59_3438 = (commit_mark_env ())
in (let _59_3440 = (varops.commit_mark ())
in (FStar_ToSMT_Z3.commit_mark msg))))

let encode_sig : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _162_2347 = (let _162_2346 = (let _162_2345 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (Prims.strcat "encoding sigelt " _162_2345))
in FStar_ToSMT_Term.Caption (_162_2346))
in (_162_2347)::decls)
end else begin
decls
end)
in (let env = (get_env tcenv)
in (let _59_3449 = (encode_sigelt env se)
in (match (_59_3449) with
| (decls, env) -> begin
(let _59_3450 = (set_env env)
in (let _162_2348 = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 _162_2348)))
end)))))

let encode_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Ident.str)
in (let _59_3455 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _162_2353 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Absyn_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "Encoding externals for %s ... %s exports\n" name _162_2353))
end else begin
()
end
in (let env = (get_env tcenv)
in (let _59_3462 = (encode_signature (let _59_3458 = env
in {bindings = _59_3458.bindings; depth = _59_3458.depth; tcenv = _59_3458.tcenv; warn = false; cache = _59_3458.cache; nolabels = _59_3458.nolabels; use_zfuel_name = _59_3458.use_zfuel_name; encode_non_total_function_typ = _59_3458.encode_non_total_function_typ}) modul.FStar_Absyn_Syntax.exports)
in (match (_59_3462) with
| (decls, env) -> begin
(let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::decls) ((FStar_ToSMT_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (let _59_3468 = (set_env (let _59_3466 = env
in {bindings = _59_3466.bindings; depth = _59_3466.depth; tcenv = _59_3466.tcenv; warn = true; cache = _59_3466.cache; nolabels = _59_3466.nolabels; use_zfuel_name = _59_3466.use_zfuel_name; encode_non_total_function_typ = _59_3466.encode_non_total_function_typ}))
in (let _59_3470 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (let decls = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

let solve : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun tcenv q -> (let _59_3475 = (let _162_2362 = (let _162_2361 = (let _162_2360 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _162_2360))
in (FStar_Util.format1 "Starting query at %s" _162_2361))
in (push _162_2362))
in (let pop = (fun _59_3478 -> (match (()) with
| () -> begin
(let _162_2367 = (let _162_2366 = (let _162_2365 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _162_2365))
in (FStar_Util.format1 "Ending query at %s" _162_2366))
in (pop _162_2367))
end))
in (let _59_3537 = (let env = (get_env tcenv)
in (let bindings = (FStar_Tc_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (let _59_3511 = (let rec aux = (fun bindings -> (match (bindings) with
| FStar_Tc_Env.Binding_var (x, t)::rest -> begin
(let _59_3493 = (aux rest)
in (match (_59_3493) with
| (out, rest) -> begin
(let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
in (((FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t)))::out, rest))
end))
end
| FStar_Tc_Env.Binding_typ (a, k)::rest -> begin
(let _59_3503 = (aux rest)
in (match (_59_3503) with
| (out, rest) -> begin
(((FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k)))::out, rest)
end))
end
| _59_3505 -> begin
([], bindings)
end))
in (let _59_3508 = (aux bindings)
in (match (_59_3508) with
| (closing, bindings) -> begin
(let _162_2372 = (FStar_Absyn_Util.close_forall (FStar_List.rev closing) q)
in (_162_2372, bindings))
end)))
in (match (_59_3511) with
| (q, bindings) -> begin
(let _59_3520 = (let _162_2374 = (FStar_List.filter (fun _59_32 -> (match (_59_32) with
| FStar_Tc_Env.Binding_sig (_59_3514) -> begin
false
end
| _59_3517 -> begin
true
end)) bindings)
in (encode_env_bindings env _162_2374))
in (match (_59_3520) with
| (env_decls, env) -> begin
(let _59_3521 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _162_2375 = (FStar_Absyn_Print.formula_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _162_2375))
end else begin
()
end
in (let _59_3526 = (encode_formula_with_labels q env)
in (match (_59_3526) with
| (phi, labels, qdecls) -> begin
(let _59_3529 = (encode_labels labels)
in (match (_59_3529) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (let qry = (let _162_2377 = (let _162_2376 = (FStar_ToSMT_Term.mkNot phi)
in (_162_2376, Some ("query")))
in FStar_ToSMT_Term.Assume (_162_2377))
in (let suffix = (FStar_List.append label_suffix ((FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))
end))))
in (match (_59_3537) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_ToSMT_Term.Assume ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (FStar_ToSMT_Term.False, _59_3544); FStar_ToSMT_Term.hash = _59_3541; FStar_ToSMT_Term.freevars = _59_3539}, _59_3549) -> begin
(let _59_3552 = (pop ())
in ())
end
| _59_3555 when tcenv.FStar_Tc_Env.admit -> begin
(let _59_3556 = (pop ())
in ())
end
| FStar_ToSMT_Term.Assume (q, _59_3560) -> begin
(let fresh = ((FStar_String.length q.FStar_ToSMT_Term.hash) >= 2048)
in (let _59_3564 = (FStar_ToSMT_Z3.giveZ3 prefix)
in (let with_fuel = (fun p _59_3570 -> (match (_59_3570) with
| (n, i) -> begin
(let _162_2400 = (let _162_2399 = (let _162_2384 = (let _162_2383 = (FStar_Util.string_of_int n)
in (let _162_2382 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _162_2383 _162_2382)))
in FStar_ToSMT_Term.Caption (_162_2384))
in (let _162_2398 = (let _162_2397 = (let _162_2389 = (let _162_2388 = (let _162_2387 = (let _162_2386 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _162_2385 = (FStar_ToSMT_Term.n_fuel n)
in (_162_2386, _162_2385)))
in (FStar_ToSMT_Term.mkEq _162_2387))
in (_162_2388, None))
in FStar_ToSMT_Term.Assume (_162_2389))
in (let _162_2396 = (let _162_2395 = (let _162_2394 = (let _162_2393 = (let _162_2392 = (let _162_2391 = (FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _162_2390 = (FStar_ToSMT_Term.n_fuel i)
in (_162_2391, _162_2390)))
in (FStar_ToSMT_Term.mkEq _162_2392))
in (_162_2393, None))
in FStar_ToSMT_Term.Assume (_162_2394))
in (_162_2395)::(p)::(FStar_ToSMT_Term.CheckSat)::[])
in (_162_2397)::_162_2396))
in (_162_2399)::_162_2398))
in (FStar_List.append _162_2400 suffix))
end))
in (let check = (fun p -> (let initial_config = (let _162_2404 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _162_2403 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_162_2404, _162_2403)))
in (let alt_configs = (let _162_2423 = (let _162_2422 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _162_2407 = (let _162_2406 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _162_2405 = (FStar_ST.read FStar_Options.max_ifuel)
in (_162_2406, _162_2405)))
in (_162_2407)::[])
end else begin
[]
end
in (let _162_2421 = (let _162_2420 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _162_2410 = (let _162_2409 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _162_2408 = (FStar_ST.read FStar_Options.max_ifuel)
in (_162_2409, _162_2408)))
in (_162_2410)::[])
end else begin
[]
end
in (let _162_2419 = (let _162_2418 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _162_2413 = (let _162_2412 = (FStar_ST.read FStar_Options.max_fuel)
in (let _162_2411 = (FStar_ST.read FStar_Options.max_ifuel)
in (_162_2412, _162_2411)))
in (_162_2413)::[])
end else begin
[]
end
in (let _162_2417 = (let _162_2416 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _162_2415 = (let _162_2414 = (FStar_ST.read FStar_Options.min_fuel)
in (_162_2414, 1))
in (_162_2415)::[])
end else begin
[]
end
in (_162_2416)::[])
in (_162_2418)::_162_2417))
in (_162_2420)::_162_2419))
in (_162_2422)::_162_2421))
in (FStar_List.flatten _162_2423))
in (let report = (fun errs -> (let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Absyn_Syntax.dummyRange))::[]
end
| _59_3579 -> begin
errs
end)
in (let _59_3581 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _162_2431 = (let _162_2426 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _162_2426))
in (let _162_2430 = (let _162_2427 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _162_2427 FStar_Util.string_of_int))
in (let _162_2429 = (let _162_2428 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _162_2428 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _162_2431 _162_2430 _162_2429))))
end else begin
()
end
in (FStar_Tc_Errors.add_errors tcenv errs))))
in (let rec try_alt_configs = (fun p errs _59_33 -> (match (_59_33) with
| [] -> begin
(report errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _162_2442 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _162_2442 (cb mi p [])))
end
| _59_3593 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _162_2444 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _162_2444 (fun _59_3599 -> (match (_59_3599) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _59_3602 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _59_3605 p alt _59_3610 -> (match ((_59_3605, _59_3610)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _162_2452 = (let _162_2449 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _162_2449))
in (let _162_2451 = (FStar_Util.string_of_int prev_fuel)
in (let _162_2450 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _162_2452 _162_2451 _162_2450))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _162_2453 = (with_fuel p initial_config)
in (FStar_ToSMT_Z3.ask fresh labels _162_2453 (cb initial_config p alt_configs))))))))
in (let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(let _59_3615 = (let _162_2459 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_ToSMT_SplitQueryCases.can_handle_query _162_2459 q))
in (match (_59_3615) with
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
in (let _59_3616 = if (FStar_ST.read FStar_Options.admit_smt_queries) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end)
end)))))

let is_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (let env = (get_env tcenv)
in (let _59_3621 = (push "query")
in (let _59_3628 = (encode_formula_with_labels q env)
in (match (_59_3628) with
| (f, _59_3625, _59_3627) -> begin
(let _59_3629 = (pop "query")
in (match (f.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _59_3633) -> begin
true
end
| _59_3637 -> begin
false
end))
end)))))

let solver : FStar_Tc_Env.solver_t = {FStar_Tc_Env.init = init; FStar_Tc_Env.push = push; FStar_Tc_Env.pop = pop; FStar_Tc_Env.mark = mark; FStar_Tc_Env.reset_mark = reset_mark; FStar_Tc_Env.commit_mark = commit_mark; FStar_Tc_Env.encode_modul = encode_modul; FStar_Tc_Env.encode_sig = encode_sig; FStar_Tc_Env.solve = solve; FStar_Tc_Env.is_trivial = is_trivial; FStar_Tc_Env.finish = FStar_ToSMT_Z3.finish; FStar_Tc_Env.refresh = FStar_ToSMT_Z3.refresh}

let dummy : FStar_Tc_Env.solver_t = {FStar_Tc_Env.init = (fun _59_3638 -> ()); FStar_Tc_Env.push = (fun _59_3640 -> ()); FStar_Tc_Env.pop = (fun _59_3642 -> ()); FStar_Tc_Env.mark = (fun _59_3644 -> ()); FStar_Tc_Env.reset_mark = (fun _59_3646 -> ()); FStar_Tc_Env.commit_mark = (fun _59_3648 -> ()); FStar_Tc_Env.encode_modul = (fun _59_3650 _59_3652 -> ()); FStar_Tc_Env.encode_sig = (fun _59_3654 _59_3656 -> ()); FStar_Tc_Env.solve = (fun _59_3658 _59_3660 -> ()); FStar_Tc_Env.is_trivial = (fun _59_3662 _59_3664 -> false); FStar_Tc_Env.finish = (fun _59_3666 -> ()); FStar_Tc_Env.refresh = (fun _59_3667 -> ())}





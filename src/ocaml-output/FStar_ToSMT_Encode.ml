
open Prims

let add_fuel = (fun x tl -> if (FStar_Options.unthrottle_inductives ()) then begin
tl
end else begin
(x)::tl
end)


let withenv = (fun c _50_39 -> (match (_50_39) with
| (a, b) -> begin
(a, b, c)
end))


let vargs = (fun args -> (FStar_List.filter (fun _50_1 -> (match (_50_1) with
| (FStar_Util.Inl (_50_43), _50_46) -> begin
false
end
| _50_49 -> begin
true
end)) args))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let escape_null_name = (fun a -> if (a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = "_") then begin
(Prims.strcat a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText a.FStar_Absyn_Syntax.realname.FStar_Ident.idText)
end else begin
a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end)


let mk_typ_projector_name : FStar_Ident.lident  ->  FStar_Absyn_Syntax.btvdef  ->  Prims.string = (fun lid a -> (let _140_14 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (escape_null_name a))
in (FStar_All.pipe_left escape _140_14)))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Absyn_Syntax.bvvdef  ->  Prims.string = (fun lid a -> (

let a = (let _140_19 = (FStar_Absyn_Util.unmangle_field_name a.FStar_Absyn_Syntax.ppname)
in {FStar_Absyn_Syntax.ppname = _140_19; FStar_Absyn_Syntax.realname = a.FStar_Absyn_Syntax.realname})
in (let _140_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (escape_null_name a))
in (FStar_All.pipe_left escape _140_20))))


let primitive_projector_by_pos : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun _50_61 -> (match (()) with
| () -> begin
(let _140_30 = (let _140_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _140_29 lid.FStar_Ident.str))
in (FStar_All.failwith _140_30))
end))
in (

let t = (FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _140_31 = (FStar_Absyn_Util.compress_typ t)
in _140_31.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _50_65) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
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
| _50_74 -> begin
(fail ())
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _140_37 = (let _140_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _140_36))
in (FStar_All.pipe_left escape _140_37)))


let mk_typ_projector : FStar_Ident.lident  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_ToSMT_Term.term = (fun lid a -> (let _140_43 = (let _140_42 = (mk_typ_projector_name lid a)
in (_140_42, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Type_sort))))
in (FStar_ToSMT_Term.mkFreeV _140_43)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_ToSMT_Term.term = (fun lid a -> (let _140_49 = (let _140_48 = (mk_term_projector_name lid a)
in (_140_48, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _140_49)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_ToSMT_Term.term = (fun lid i -> (let _140_55 = (let _140_54 = (mk_term_projector_name_by_pos lid i)
in (_140_54, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _140_55)))


let mk_data_tester = (fun env l x -> (FStar_ToSMT_Term.mk_tester (escape l.FStar_Ident.str) x))


type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  FStar_Ident.ident  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_ToSMT_Term.term; next_id : Prims.unit  ->  Prims.int}


let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))


let varops : varops_t = (

let initial_ctr = 10
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun _50_100 -> (match (()) with
| () -> begin
(let _140_159 = (FStar_Util.smap_create 100)
in (let _140_158 = (FStar_Util.smap_create 100)
in (_140_159, _140_158)))
end))
in (

let scopes = (let _140_161 = (let _140_160 = (new_scope ())
in (_140_160)::[])
in (FStar_Util.mk_ref _140_161))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _140_165 = (FStar_ST.read scopes)
in (FStar_Util.find_map _140_165 (fun _50_108 -> (match (_50_108) with
| (names, _50_107) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_50_111) -> begin
(

let _50_113 = (FStar_Util.incr ctr)
in (let _140_167 = (let _140_166 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _140_166))
in (Prims.strcat (Prims.strcat y "__") _140_167)))
end)
in (

let top_scope = (let _140_169 = (let _140_168 = (FStar_ST.read scopes)
in (FStar_List.hd _140_168))
in (FStar_All.pipe_left Prims.fst _140_169))
in (

let _50_117 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (let _140_175 = (let _140_174 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _140_174 "__"))
in (Prims.strcat _140_175 rn.FStar_Ident.idText)))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun _50_125 -> (match (()) with
| () -> begin
(

let _50_126 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (

let fresh = (fun pfx -> (let _140_183 = (let _140_182 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _140_182))
in (FStar_Util.format2 "%s_%s" pfx _140_183)))
in (

let string_const = (fun s -> (match ((let _140_187 = (FStar_ST.read scopes)
in (FStar_Util.find_map _140_187 (fun _50_135 -> (match (_50_135) with
| (_50_133, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _140_188 = (FStar_ToSMT_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxString _140_188))
in (

let top_scope = (let _140_190 = (let _140_189 = (FStar_ST.read scopes)
in (FStar_List.hd _140_189))
in (FStar_All.pipe_left Prims.snd _140_190))
in (

let _50_142 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _50_145 -> (match (()) with
| () -> begin
(let _140_195 = (let _140_194 = (new_scope ())
in (let _140_193 = (FStar_ST.read scopes)
in (_140_194)::_140_193))
in (FStar_ST.op_Colon_Equals scopes _140_195))
end))
in (

let pop = (fun _50_147 -> (match (()) with
| () -> begin
(let _140_199 = (let _140_198 = (FStar_ST.read scopes)
in (FStar_List.tl _140_198))
in (FStar_ST.op_Colon_Equals scopes _140_199))
end))
in (

let mark = (fun _50_149 -> (match (()) with
| () -> begin
(push ())
end))
in (

let reset_mark = (fun _50_151 -> (match (()) with
| () -> begin
(pop ())
end))
in (

let commit_mark = (fun _50_153 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
(

let _50_166 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (

let _50_171 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _50_174 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))


let unmangle = (fun x -> (let _140_215 = (let _140_214 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.ppname)
in (let _140_213 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.realname)
in (_140_214, _140_213)))
in (FStar_Absyn_Util.mkbvd _140_215)))


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
| Binding_var (_50_179) -> begin
_50_179
end))


let ___Binding_tvar____0 = (fun projectee -> (match (projectee) with
| Binding_tvar (_50_182) -> begin
_50_182
end))


let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_50_185) -> begin
_50_185
end))


let ___Binding_ftvar____0 = (fun projectee -> (match (projectee) with
| Binding_ftvar (_50_188) -> begin
_50_188
end))


let binder_of_eithervar = (fun v -> (v, None))


type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_Tc_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_ToSMT_Term.sort Prims.list * FStar_ToSMT_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))


let print_env : env_t  ->  Prims.string = (fun e -> (let _140_301 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _50_2 -> (match (_50_2) with
| Binding_var (x, t) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Binding_tvar (a, t) -> begin
(FStar_Absyn_Print.strBvd a)
end
| Binding_fvar (l, s, t, _50_213) -> begin
(FStar_Absyn_Print.sli l)
end
| Binding_ftvar (l, s, t) -> begin
(FStar_Absyn_Print.sli l)
end))))
in (FStar_All.pipe_right _140_301 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string Prims.option = (fun env t -> if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _140_311 = (FStar_Absyn_Print.typ_to_string t)
in Some (_140_311))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_ToSMT_Term.sort  ->  (Prims.string * FStar_ToSMT_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _140_316 = (FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _140_316))))


let gen_term_var : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (

let ysym = (let _140_321 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _140_321))
in (

let y = (FStar_ToSMT_Term.mkFreeV (ysym, FStar_ToSMT_Term.Term_sort))
in (ysym, y, (

let _50_232 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _50_232.tcenv; warn = _50_232.warn; cache = _50_232.cache; nolabels = _50_232.nolabels; use_zfuel_name = _50_232.use_zfuel_name; encode_non_total_function_typ = _50_232.encode_non_total_function_typ})))))


let new_term_constant : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (

let y = (FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (

let _50_238 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _50_238.depth; tcenv = _50_238.tcenv; warn = _50_238.warn; cache = _50_238.cache; nolabels = _50_238.nolabels; use_zfuel_name = _50_238.use_zfuel_name; encode_non_total_function_typ = _50_238.encode_non_total_function_typ})))))


let push_term_var : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_ToSMT_Term.term  ->  env_t = (fun env x t -> (

let _50_243 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _50_243.depth; tcenv = _50_243.tcenv; warn = _50_243.warn; cache = _50_243.cache; nolabels = _50_243.nolabels; use_zfuel_name = _50_243.use_zfuel_name; encode_non_total_function_typ = _50_243.encode_non_total_function_typ}))


let lookup_term_var = (fun env a -> (match ((lookup_binding env (fun _50_3 -> (match (_50_3) with
| Binding_var (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _50_253 -> begin
None
end)))) with
| None -> begin
(let _140_336 = (let _140_335 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound term variable not found: %s" _140_335))
in (FStar_All.failwith _140_336))
end
| Some (b, t) -> begin
t
end))


let gen_typ_var : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (

let ysym = (let _140_341 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@a" _140_341))
in (

let y = (FStar_ToSMT_Term.mkFreeV (ysym, FStar_ToSMT_Term.Type_sort))
in (ysym, y, (

let _50_263 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _50_263.tcenv; warn = _50_263.warn; cache = _50_263.cache; nolabels = _50_263.nolabels; use_zfuel_name = _50_263.use_zfuel_name; encode_non_total_function_typ = _50_263.encode_non_total_function_typ})))))


let new_typ_constant : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (

let y = (FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (

let _50_269 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = _50_269.depth; tcenv = _50_269.tcenv; warn = _50_269.warn; cache = _50_269.cache; nolabels = _50_269.nolabels; use_zfuel_name = _50_269.use_zfuel_name; encode_non_total_function_typ = _50_269.encode_non_total_function_typ})))))


let push_typ_var : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_ToSMT_Term.term  ->  env_t = (fun env x t -> (

let _50_274 = env
in {bindings = (Binding_tvar ((x, t)))::env.bindings; depth = _50_274.depth; tcenv = _50_274.tcenv; warn = _50_274.warn; cache = _50_274.cache; nolabels = _50_274.nolabels; use_zfuel_name = _50_274.use_zfuel_name; encode_non_total_function_typ = _50_274.encode_non_total_function_typ}))


let lookup_typ_var = (fun env a -> (match ((lookup_binding env (fun _50_4 -> (match (_50_4) with
| Binding_tvar (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _50_284 -> begin
None
end)))) with
| None -> begin
(let _140_356 = (let _140_355 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound type variable not found: %s" _140_355))
in (FStar_All.failwith _140_356))
end
| Some (b, t) -> begin
t
end))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (let _140_367 = (

let _50_294 = env
in (let _140_366 = (let _140_365 = (let _140_364 = (let _140_363 = (let _140_362 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _140_361 -> Some (_140_361)) _140_362))
in (x, fname, _140_363, None))
in Binding_fvar (_140_364))
in (_140_365)::env.bindings)
in {bindings = _140_366; depth = _50_294.depth; tcenv = _50_294.tcenv; warn = _50_294.warn; cache = _50_294.cache; nolabels = _50_294.nolabels; use_zfuel_name = _50_294.use_zfuel_name; encode_non_total_function_typ = _50_294.encode_non_total_function_typ}))
in (fname, ftok, _140_367)))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _50_5 -> (match (_50_5) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _50_306 -> begin
None
end))))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _140_378 = (let _140_377 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Name not found: %s" _140_377))
in (FStar_All.failwith _140_378))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _50_316 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _50_316.depth; tcenv = _50_316.tcenv; warn = _50_316.warn; cache = _50_316.cache; nolabels = _50_316.nolabels; use_zfuel_name = _50_316.use_zfuel_name; encode_non_total_function_typ = _50_316.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _50_325 = (lookup_lid env x)
in (match (_50_325) with
| (t1, t2, _50_324) -> begin
(

let t3 = (let _140_395 = (let _140_394 = (let _140_393 = (FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_140_393)::[])
in (f, _140_394))
in (FStar_ToSMT_Term.mkApp _140_395))
in (

let _50_327 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _50_327.depth; tcenv = _50_327.tcenv; warn = _50_327.warn; cache = _50_327.cache; nolabels = _50_327.nolabels; use_zfuel_name = _50_327.use_zfuel_name; encode_non_total_function_typ = _50_327.encode_non_total_function_typ}))
end)))


let lookup_free_var = (fun env a -> (

let _50_334 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_50_334) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
f
end
| _50_338 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (_50_342, (fuel)::[]) -> begin
if (let _140_399 = (let _140_398 = (FStar_ToSMT_Term.fv_of_term fuel)
in (FStar_All.pipe_right _140_398 Prims.fst))
in (FStar_Util.starts_with _140_399 "fuel")) then begin
(let _140_400 = (FStar_ToSMT_Term.mkFreeV (name, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_ApplyEF _140_400 fuel))
end else begin
t
end
end
| _50_348 -> begin
t
end)
end
| _50_350 -> begin
(let _140_402 = (let _140_401 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _140_401))
in (FStar_All.failwith _140_402))
end)
end)
end)))


let lookup_free_var_name = (fun env a -> (

let _50_358 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_50_358) with
| (x, _50_355, _50_357) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _50_364 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_50_364) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (g, zf); FStar_ToSMT_Term.hash = _50_368; FStar_ToSMT_Term.freevars = _50_366}) when env.use_zfuel_name -> begin
(g, zf)
end
| _50_376 -> begin
(match (sym) with
| None -> begin
(FStar_ToSMT_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (g, (fuel)::[]) -> begin
(g, (fuel)::[])
end
| _50_386 -> begin
(FStar_ToSMT_Term.Var (name), [])
end)
end)
end)
end)))


let new_typ_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (let _140_417 = (

let _50_391 = env
in (let _140_416 = (let _140_415 = (let _140_414 = (let _140_413 = (let _140_412 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _140_411 -> Some (_140_411)) _140_412))
in (x, fname, _140_413))
in Binding_ftvar (_140_414))
in (_140_415)::env.bindings)
in {bindings = _140_416; depth = _50_391.depth; tcenv = _50_391.tcenv; warn = _50_391.warn; cache = _50_391.cache; nolabels = _50_391.nolabels; use_zfuel_name = _50_391.use_zfuel_name; encode_non_total_function_typ = _50_391.encode_non_total_function_typ}))
in (fname, ftok, _140_417)))))


let lookup_tlid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option) = (fun env a -> (match ((lookup_binding env (fun _50_6 -> (match (_50_6) with
| Binding_ftvar (b, t1, t2) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2))
end
| _50_402 -> begin
None
end)))) with
| None -> begin
(let _140_424 = (let _140_423 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Type name not found: %s" _140_423))
in (FStar_All.failwith _140_424))
end
| Some (s) -> begin
s
end))


let push_free_tvar : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _50_410 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _50_410.depth; tcenv = _50_410.tcenv; warn = _50_410.warn; cache = _50_410.cache; nolabels = _50_410.nolabels; use_zfuel_name = _50_410.use_zfuel_name; encode_non_total_function_typ = _50_410.encode_non_total_function_typ}))


let lookup_free_tvar = (fun env a -> (match ((let _140_435 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _140_435 Prims.snd))) with
| None -> begin
(let _140_437 = (let _140_436 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Type name not found: %s" _140_436))
in (FStar_All.failwith _140_437))
end
| Some (t) -> begin
t
end))


let lookup_free_tvar_name = (fun env a -> (let _140_440 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _140_440 Prims.fst)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _50_7 -> (match (_50_7) with
| (Binding_fvar (_, nm', tok, _)) | (Binding_ftvar (_, nm', tok)) when (nm = nm') -> begin
tok
end
| _50_435 -> begin
None
end))))


let mkForall_fuel' = (fun n _50_440 -> (match (_50_440) with
| (pats, vars, body) -> begin
(

let fallback = (fun _50_442 -> (match (()) with
| () -> begin
(FStar_ToSMT_Term.mkForall (pats, vars, body))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _50_445 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_50_445) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var ("HasType"), args) -> begin
(FStar_ToSMT_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _50_455 -> begin
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
(let _140_453 = (add_fuel guards)
in (FStar_ToSMT_Term.mk_and_l _140_453))
end
| _50_468 -> begin
(let _140_454 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _140_454 FStar_List.hd))
end)
in (FStar_ToSMT_Term.mkImp (guard, body')))
end
| _50_471 -> begin
body
end)
in (

let vars = ((fsym, FStar_ToSMT_Term.Fuel_sort))::vars
in (FStar_ToSMT_Term.mkForall (pats, vars, body))))))
end))
end)
end))


let mkForall_fuel : (FStar_ToSMT_Term.pat Prims.list Prims.list * FStar_ToSMT_Term.fvs * FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term = (mkForall_fuel' 1)


let head_normal : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun env t -> (

let t = (FStar_Absyn_Util.unmeta_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_refine (_)) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| (FStar_Absyn_Syntax.Typ_const (v)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (v); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _140_460 = (FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _140_460 FStar_Option.isNone))
end
| _50_509 -> begin
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


let trivial_post : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun t -> (let _140_482 = (let _140_481 = (let _140_479 = (FStar_Absyn_Syntax.null_v_binder t)
in (_140_479)::[])
in (let _140_480 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (_140_481, _140_480)))
in (FStar_Absyn_Syntax.mk_Typ_lam _140_482 None t.FStar_Absyn_Syntax.pos)))


let mk_ApplyE : FStar_ToSMT_Term.term  ->  (Prims.string * FStar_ToSMT_Term.sort) Prims.list  ->  FStar_ToSMT_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _140_489 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyET out _140_489))
end
| FStar_ToSMT_Term.Fuel_sort -> begin
(let _140_490 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEF out _140_490))
end
| _50_526 -> begin
(let _140_491 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEE out _140_491))
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
(let _140_504 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTT out _140_504))
end
| _50_541 -> begin
(let _140_505 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTE out _140_505))
end)) t)))


let mk_ApplyT_args : FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list  ->  FStar_ToSMT_Term.term = (fun t args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out arg -> (match (arg) with
| FStar_Util.Inl (t) -> begin
(FStar_ToSMT_Term.mk_ApplyTT out t)
end
| FStar_Util.Inr (e) -> begin
(FStar_ToSMT_Term.mk_ApplyTE out e)
end)) t)))


let is_app : FStar_ToSMT_Term.op  ->  Prims.bool = (fun _50_8 -> (match (_50_8) with
| (FStar_ToSMT_Term.Var ("ApplyTT")) | (FStar_ToSMT_Term.Var ("ApplyTE")) | (FStar_ToSMT_Term.Var ("ApplyET")) | (FStar_ToSMT_Term.Var ("ApplyEE")) -> begin
true
end
| _50_560 -> begin
false
end))


let is_eta : env_t  ->  FStar_ToSMT_Term.fv Prims.list  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match ((t.FStar_ToSMT_Term.tm, xs)) with
| (FStar_ToSMT_Term.App (app, (f)::({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.FreeV (y); FStar_ToSMT_Term.hash = _50_571; FStar_ToSMT_Term.freevars = _50_569})::[]), (x)::xs) when ((is_app app) && (FStar_ToSMT_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var (f), args), _50_589) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (fv) -> begin
(FStar_ToSMT_Term.fv_eq fv v)
end
| _50_596 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_50_598, []) -> begin
(

let fvs = (FStar_ToSMT_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_ToSMT_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _50_604 -> begin
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


let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable (_) -> begin
true
end
| _ -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_ToSMT_Term.term = (fun _50_9 -> (match (_50_9) with
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
(let _140_564 = (let _140_563 = (let _140_562 = (let _140_561 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_ToSMT_Term.boxInt _140_561))
in (_140_562)::[])
in ("FStar.Char.Char", _140_563))
in (FStar_ToSMT_Term.mkApp _140_564))
end
| FStar_Const.Const_int (i, None) -> begin
(let _140_565 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _140_565))
end
| FStar_Const.Const_int (i, Some (_50_624)) -> begin
(FStar_All.failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, _50_630) -> begin
(let _140_566 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _140_566))
end
| c -> begin
(let _140_568 = (let _140_567 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s\n" _140_567))
in (FStar_All.failwith _140_568))
end))


let as_function_typ : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_50_641) -> begin
t
end
| FStar_Absyn_Syntax.Typ_refine (_50_644) -> begin
(let _140_577 = (FStar_Absyn_Util.unrefine t)
in (aux true _140_577))
end
| _50_647 -> begin
if norm then begin
(let _140_578 = (whnf env t)
in (aux false _140_578))
end else begin
(let _140_581 = (let _140_580 = (FStar_Range.string_of_range t0.FStar_Absyn_Syntax.pos)
in (let _140_579 = (FStar_Absyn_Print.typ_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _140_580 _140_579)))
in (FStar_All.failwith _140_581))
end
end)))
in (aux true t0)))


let rec encode_knd_term : FStar_Absyn_Syntax.knd  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun k env -> (match ((let _140_618 = (FStar_Absyn_Util.compress_kind k)
in _140_618.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
(FStar_ToSMT_Term.mk_Kind_type, [])
end
| FStar_Absyn_Syntax.Kind_abbrev (_50_652, k0) -> begin
(

let _50_656 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _140_620 = (FStar_Absyn_Print.kind_to_string k)
in (let _140_619 = (FStar_Absyn_Print.kind_to_string k0)
in (FStar_Util.print2 "Encoding kind abbrev %s, expanded to %s\n" _140_620 _140_619)))
end else begin
()
end
in (encode_knd_term k0 env))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, _50_660) -> begin
(let _140_622 = (let _140_621 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Kind_uvar _140_621))
in (_140_622, []))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, kbody) -> begin
(

let tsym = (let _140_623 = (varops.fresh "t")
in (_140_623, FStar_ToSMT_Term.Type_sort))
in (

let t = (FStar_ToSMT_Term.mkFreeV tsym)
in (

let _50_675 = (encode_binders None bs env)
in (match (_50_675) with
| (vars, guards, env', decls, _50_674) -> begin
(

let app = (mk_ApplyT t vars)
in (

let _50_679 = (encode_knd kbody env' app)
in (match (_50_679) with
| (kbody, decls') -> begin
(

let rec aux = (fun app vars guards -> (match ((vars, guards)) with
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
| _50_698 -> begin
(let _140_632 = (let _140_631 = (let _140_630 = (FStar_ToSMT_Term.mk_PreKind app)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _140_630))
in (_140_631, body))
in (FStar_ToSMT_Term.mkAnd _140_632))
end)
in (let _140_634 = (let _140_633 = (FStar_ToSMT_Term.mkImp (g, body))
in (((app)::[])::[], (x)::[], _140_633))
in (FStar_ToSMT_Term.mkForall _140_634)))))
end
| _50_701 -> begin
(FStar_All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (

let k_interp = (aux t vars guards)
in (

let cvars = (let _140_636 = (FStar_ToSMT_Term.free_variables k_interp)
in (FStar_All.pipe_right _140_636 (FStar_List.filter (fun _50_706 -> (match (_50_706) with
| (x, _50_705) -> begin
(x <> (Prims.fst tsym))
end)))))
in (

let tkey = (FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (k', sorts, _50_712) -> begin
(let _140_639 = (let _140_638 = (let _140_637 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (k', _140_637))
in (FStar_ToSMT_Term.mkApp _140_638))
in (_140_639, []))
end
| None -> begin
(

let ksym = (varops.fresh "Kind_arrow")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _140_640 = (FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_140_640))
end else begin
None
end
in (

let kdecl = FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, FStar_ToSMT_Term.Kind_sort, caption))
in (

let k = (let _140_642 = (let _140_641 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _140_641))
in (FStar_ToSMT_Term.mkApp _140_642))
in (

let t_has_k = (FStar_ToSMT_Term.mk_HasKind t k)
in (

let k_interp = (let _140_651 = (let _140_650 = (let _140_649 = (let _140_648 = (let _140_647 = (let _140_646 = (let _140_645 = (let _140_644 = (let _140_643 = (FStar_ToSMT_Term.mk_PreKind t)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _140_643))
in (_140_644, k_interp))
in (FStar_ToSMT_Term.mkAnd _140_645))
in (t_has_k, _140_646))
in (FStar_ToSMT_Term.mkIff _140_647))
in (((t_has_k)::[])::[], (tsym)::cvars, _140_648))
in (FStar_ToSMT_Term.mkForall _140_649))
in (_140_650, Some ((Prims.strcat ksym " interpretation"))))
in FStar_ToSMT_Term.Assume (_140_651))
in (

let k_decls = (FStar_List.append (FStar_List.append decls decls') ((kdecl)::(k_interp)::[]))
in (

let _50_724 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _50_727 -> begin
(let _140_653 = (let _140_652 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.format1 "Unknown kind: %s" _140_652))
in (FStar_All.failwith _140_653))
end))
and encode_knd : FStar_Absyn_Syntax.knd  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decl Prims.list) = (fun k env t -> (

let _50_733 = (encode_knd_term k env)
in (match (_50_733) with
| (k, decls) -> begin
(let _140_657 = (FStar_ToSMT_Term.mk_HasKind t k)
in (_140_657, decls))
end)))
and encode_binders : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.binders  ->  env_t  ->  (FStar_ToSMT_Term.fv Prims.list * FStar_ToSMT_Term.term Prims.list * env_t * FStar_ToSMT_Term.decls_t * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list) = (fun fuel_opt bs env -> (

let _50_737 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _140_661 = (FStar_Absyn_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _140_661))
end else begin
()
end
in (

let _50_787 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _50_744 b -> (match (_50_744) with
| (vars, guards, env, decls, names) -> begin
(

let _50_781 = (match ((Prims.fst b)) with
| FStar_Util.Inl ({FStar_Absyn_Syntax.v = a; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _50_747}) -> begin
(

let a = (unmangle a)
in (

let _50_756 = (gen_typ_var env a)
in (match (_50_756) with
| (aasym, aa, env') -> begin
(

let _50_757 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _140_665 = (FStar_Absyn_Print.strBvd a)
in (let _140_664 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.print3 "Encoding type binder %s (%s) at kind %s\n" _140_665 aasym _140_664)))
end else begin
()
end
in (

let _50_761 = (encode_knd k env aa)
in (match (_50_761) with
| (guard_a_k, decls') -> begin
((aasym, FStar_ToSMT_Term.Type_sort), guard_a_k, env', decls', FStar_Util.Inl (a))
end)))
end)))
end
| FStar_Util.Inr ({FStar_Absyn_Syntax.v = x; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _50_763}) -> begin
(

let x = (unmangle x)
in (

let _50_772 = (gen_term_var env x)
in (match (_50_772) with
| (xxsym, xx, env') -> begin
(

let _50_775 = (let _140_666 = (norm_t env t)
in (encode_typ_pred fuel_opt _140_666 env xx))
in (match (_50_775) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_ToSMT_Term.Term_sort), guard_x_t, env', decls', FStar_Util.Inr (x))
end))
end)))
end)
in (match (_50_781) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_50_787) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_typ_pred : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun fuel_opt t env e -> (

let t = (FStar_Absyn_Util.compress_typ t)
in (

let _50_795 = (encode_typ_term t env)
in (match (_50_795) with
| (t, decls) -> begin
(let _140_671 = (FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_140_671, decls))
end))))
and encode_typ_pred' : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun fuel_opt t env e -> (

let t = (FStar_Absyn_Util.compress_typ t)
in (

let _50_803 = (encode_typ_term t env)
in (match (_50_803) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _140_676 = (FStar_ToSMT_Term.mk_HasTypeZ e t)
in (_140_676, decls))
end
| Some (f) -> begin
(let _140_677 = (FStar_ToSMT_Term.mk_HasTypeFuel f e t)
in (_140_677, decls))
end)
end))))
and encode_typ_term : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Absyn_Util.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _140_680 = (lookup_typ_var env a)
in (_140_680, []))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _140_681 = (lookup_free_tvar env fv)
in (_140_681, []))
end
| FStar_Absyn_Syntax.Typ_fun (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (FStar_Absyn_Util.is_tot_or_gtot_comp res)) then begin
(

let _50_824 = (encode_binders None binders env)
in (match (_50_824) with
| (vars, guards, env', decls, _50_823) -> begin
(

let fsym = (let _140_682 = (varops.fresh "f")
in (_140_682, FStar_ToSMT_Term.Term_sort))
in (

let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (

let app = (mk_ApplyE f vars)
in (

let _50_830 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_50_830) with
| (pre_opt, res_t) -> begin
(

let _50_833 = (encode_typ_pred None res_t env' app)
in (match (_50_833) with
| (res_pred, decls') -> begin
(

let _50_842 = (match (pre_opt) with
| None -> begin
(let _140_683 = (FStar_ToSMT_Term.mk_and_l guards)
in (_140_683, decls))
end
| Some (pre) -> begin
(

let _50_839 = (encode_formula pre env')
in (match (_50_839) with
| (guard, decls0) -> begin
(let _140_684 = (FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_140_684, (FStar_List.append decls decls0)))
end))
end)
in (match (_50_842) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _140_686 = (let _140_685 = (FStar_ToSMT_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _140_685))
in (FStar_ToSMT_Term.mkForall _140_686))
in (

let cvars = (let _140_688 = (FStar_ToSMT_Term.free_variables t_interp)
in (FStar_All.pipe_right _140_688 (FStar_List.filter (fun _50_847 -> (match (_50_847) with
| (x, _50_846) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t', sorts, _50_853) -> begin
(let _140_691 = (let _140_690 = (let _140_689 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t', _140_689))
in (FStar_ToSMT_Term.mkApp _140_690))
in (_140_691, []))
end
| None -> begin
(

let tsym = (varops.fresh "Typ_fun")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _140_692 = (FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_140_692))
end else begin
None
end
in (

let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, caption))
in (

let t = (let _140_694 = (let _140_693 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _140_693))
in (FStar_ToSMT_Term.mkApp _140_694))
in (

let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (

let k_assumption = (let _140_696 = (let _140_695 = (FStar_ToSMT_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_140_695, Some ((Prims.strcat tsym " kinding"))))
in FStar_ToSMT_Term.Assume (_140_696))
in (

let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_ToSMT_Term.mk_HasTypeZ f t)
in (

let pre_typing = (let _140_703 = (let _140_702 = (let _140_701 = (let _140_700 = (let _140_699 = (let _140_698 = (let _140_697 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _140_697))
in (f_has_t, _140_698))
in (FStar_ToSMT_Term.mkImp _140_699))
in (((f_has_t)::[])::[], (fsym)::cvars, _140_700))
in (mkForall_fuel _140_701))
in (_140_702, Some ("pre-typing for functions")))
in FStar_ToSMT_Term.Assume (_140_703))
in (

let t_interp = (let _140_707 = (let _140_706 = (let _140_705 = (let _140_704 = (FStar_ToSMT_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _140_704))
in (FStar_ToSMT_Term.mkForall _140_705))
in (_140_706, Some ((Prims.strcat tsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_140_707))
in (

let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (

let _50_869 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(

let tsym = (varops.fresh "Non_total_Typ_fun")
in (

let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, [], FStar_ToSMT_Term.Type_sort, None))
in (

let t = (FStar_ToSMT_Term.mkApp (tsym, []))
in (

let t_kinding = (let _140_709 = (let _140_708 = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (_140_708, None))
in FStar_ToSMT_Term.Assume (_140_709))
in (

let fsym = ("f", FStar_ToSMT_Term.Term_sort)
in (

let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (

let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (

let t_interp = (let _140_716 = (let _140_715 = (let _140_714 = (let _140_713 = (let _140_712 = (let _140_711 = (let _140_710 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _140_710))
in (f_has_t, _140_711))
in (FStar_ToSMT_Term.mkImp _140_712))
in (((f_has_t)::[])::[], (fsym)::[], _140_713))
in (mkForall_fuel _140_714))
in (_140_715, Some ("pre-typing")))
in FStar_ToSMT_Term.Assume (_140_716))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end
| FStar_Absyn_Syntax.Typ_refine (_50_880) -> begin
(

let _50_899 = (match ((FStar_Tc_Normalize.normalize_refinement [] env.tcenv t0)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_refine (x, f); FStar_Absyn_Syntax.tk = _50_889; FStar_Absyn_Syntax.pos = _50_887; FStar_Absyn_Syntax.fvs = _50_885; FStar_Absyn_Syntax.uvs = _50_883} -> begin
(x, f)
end
| _50_896 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_50_899) with
| (x, f) -> begin
(

let _50_902 = (encode_typ_term x.FStar_Absyn_Syntax.sort env)
in (match (_50_902) with
| (base_t, decls) -> begin
(

let _50_906 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_50_906) with
| (x, xtm, env') -> begin
(

let _50_909 = (encode_formula f env')
in (match (_50_909) with
| (refinement, decls') -> begin
(

let _50_912 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_50_912) with
| (fsym, fterm) -> begin
(

let encoding = (let _140_718 = (let _140_717 = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_140_717, refinement))
in (FStar_ToSMT_Term.mkAnd _140_718))
in (

let cvars = (let _140_720 = (FStar_ToSMT_Term.free_variables encoding)
in (FStar_All.pipe_right _140_720 (FStar_List.filter (fun _50_917 -> (match (_50_917) with
| (y, _50_916) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = (x, FStar_ToSMT_Term.Term_sort)
in (

let ffv = (fsym, FStar_ToSMT_Term.Fuel_sort)
in (

let tkey = (FStar_ToSMT_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _50_924, _50_926) -> begin
(let _140_723 = (let _140_722 = (let _140_721 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t, _140_721))
in (FStar_ToSMT_Term.mkApp _140_722))
in (_140_723, []))
end
| None -> begin
(

let tsym = (varops.fresh "Typ_refine")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, None))
in (

let t = (let _140_725 = (let _140_724 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _140_724))
in (FStar_ToSMT_Term.mkApp _140_725))
in (

let x_has_t = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (

let t_kinding = (FStar_ToSMT_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (

let assumption = (let _140_727 = (let _140_726 = (FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _140_726))
in (FStar_ToSMT_Term.mkForall _140_727))
in (

let t_decls = (let _140_734 = (let _140_733 = (let _140_732 = (let _140_731 = (let _140_730 = (let _140_729 = (let _140_728 = (FStar_Absyn_Print.typ_to_string t0)
in Some (_140_728))
in (assumption, _140_729))
in FStar_ToSMT_Term.Assume (_140_730))
in (_140_731)::[])
in (FStar_ToSMT_Term.Assume ((t_kinding, None)))::_140_732)
in (tdecl)::_140_733)
in (FStar_List.append (FStar_List.append decls decls') _140_734))
in (

let _50_939 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(

let ttm = (let _140_735 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _140_735))
in (

let _50_948 = (encode_knd k env ttm)
in (match (_50_948) with
| (t_has_k, decls) -> begin
(

let d = FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(

let is_full_app = (fun _50_955 -> (match (()) with
| () -> begin
(

let kk = (FStar_Tc_Recheck.recompute_kind head)
in (

let _50_960 = (FStar_Absyn_Util.kind_formals kk)
in (match (_50_960) with
| (formals, _50_959) -> begin
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

let _50_967 = (encode_args args env)
in (match (_50_967) with
| (args, decls) -> begin
(

let t = (mk_ApplyT_args head args)
in (t, decls))
end)))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(

let _50_973 = (encode_args args env)
in (match (_50_973) with
| (args, decls) -> begin
if (is_full_app ()) then begin
(

let head = (lookup_free_tvar_name env fv)
in (

let t = (let _140_740 = (let _140_739 = (FStar_List.map (fun _50_10 -> (match (_50_10) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (head, _140_739))
in (FStar_ToSMT_Term.mkApp _140_740))
in (t, decls)))
end else begin
(

let head = (lookup_free_tvar env fv)
in (

let t = (mk_ApplyT_args head args)
in (t, decls)))
end
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(

let ttm = (let _140_741 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _140_741))
in (

let _50_989 = (encode_knd k env ttm)
in (match (_50_989) with
| (t_has_k, decls) -> begin
(

let d = FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| _50_992 -> begin
(

let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, body) -> begin
(

let _50_1004 = (encode_binders None bs env)
in (match (_50_1004) with
| (vars, guards, env, decls, _50_1003) -> begin
(

let _50_1007 = (encode_typ_term body env)
in (match (_50_1007) with
| (body, decls') -> begin
(

let key_body = (let _140_745 = (let _140_744 = (let _140_743 = (let _140_742 = (FStar_ToSMT_Term.mk_and_l guards)
in (_140_742, body))
in (FStar_ToSMT_Term.mkImp _140_743))
in ([], vars, _140_744))
in (FStar_ToSMT_Term.mkForall _140_745))
in (

let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (

let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _50_1013, _50_1015) -> begin
(let _140_748 = (let _140_747 = (let _140_746 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _140_746))
in (FStar_ToSMT_Term.mkApp _140_747))
in (_140_748, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (head) -> begin
(head, [])
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tsym = (varops.fresh "Typ_lam")
in (

let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, None))
in (

let t = (let _140_750 = (let _140_749 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _140_749))
in (FStar_ToSMT_Term.mkApp _140_750))
in (

let app = (mk_ApplyT t vars)
in (

let interp = (let _140_757 = (let _140_756 = (let _140_755 = (let _140_754 = (let _140_753 = (let _140_752 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _140_751 = (FStar_ToSMT_Term.mkEq (app, body))
in (_140_752, _140_751)))
in (FStar_ToSMT_Term.mkImp _140_753))
in (((app)::[])::[], (FStar_List.append vars cvars), _140_754))
in (FStar_ToSMT_Term.mkForall _140_755))
in (_140_756, Some ("Typ_lam interpretation")))
in FStar_ToSMT_Term.Assume (_140_757))
in (

let kinding = (

let _50_1030 = (let _140_758 = (FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _140_758 env t))
in (match (_50_1030) with
| (ktm, decls'') -> begin
(let _140_762 = (let _140_761 = (let _140_760 = (let _140_759 = (FStar_ToSMT_Term.mkForall (((t)::[])::[], cvars, ktm))
in (_140_759, Some ("Typ_lam kinding")))
in FStar_ToSMT_Term.Assume (_140_760))
in (_140_761)::[])
in (FStar_List.append decls'' _140_762))
end))
in (

let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(interp)::kinding))
in (

let _50_1033 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))
end)
end))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _50_1037) -> begin
(encode_typ_term t env)
end
| FStar_Absyn_Syntax.Typ_meta (_50_1041) -> begin
(let _140_763 = (FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _140_763 env))
end
| (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _140_768 = (let _140_767 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Absyn_Syntax.pos)
in (let _140_766 = (FStar_Absyn_Print.tag_of_typ t0)
in (let _140_765 = (FStar_Absyn_Print.typ_to_string t0)
in (let _140_764 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _140_767 _140_766 _140_765 _140_764)))))
in (FStar_All.failwith _140_768))
end)))
and encode_exp : FStar_Absyn_Syntax.exp  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun e env -> (

let e = (FStar_Absyn_Visit.compress_exp_uvars e)
in (

let e0 = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_50_1052) -> begin
(let _140_771 = (FStar_Absyn_Util.compress_exp e)
in (encode_exp _140_771 env))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(

let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Absyn_Syntax.Exp_fvar (v, _50_1059) -> begin
(let _140_772 = (lookup_free_var env v)
in (_140_772, []))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _140_773 = (encode_const c)
in (_140_773, []))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _50_1067) -> begin
(

let _50_1070 = (FStar_ST.op_Colon_Equals e.FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _50_1074)) -> begin
(encode_exp e env)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, _50_1080) -> begin
(

let e = (let _140_774 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Exp_uvar _140_774))
in (e, []))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(

let fallback = (fun _50_1089 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Exp_abs")
in (

let decl = FStar_ToSMT_Term.DeclFun ((f, [], FStar_ToSMT_Term.Term_sort, None))
in (let _140_777 = (FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
in (_140_777, (decl)::[]))))
end))
in (match ((FStar_ST.read e.FStar_Absyn_Syntax.tk)) with
| None -> begin
(

let _50_1093 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
if (let _140_778 = (FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (FStar_All.pipe_left Prims.op_Negation _140_778)) then begin
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

let _50_1105 = (FStar_Util.first_N nformals bs)
in (match (_50_1105) with
| (bs0, rest) -> begin
(

let res_t = (match ((FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s (FStar_Absyn_Util.comp_result c))
end
| _50_1109 -> begin
(FStar_All.failwith "Impossible")
end)
in (

let e = (let _140_780 = (let _140_779 = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.FStar_Absyn_Syntax.pos)
in (bs0, _140_779))
in (FStar_Absyn_Syntax.mk_Exp_abs _140_780 (Some (tfun)) e0.FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end else begin
(

let _50_1118 = (encode_binders None bs env)
in (match (_50_1118) with
| (vars, guards, envbody, decls, _50_1117) -> begin
(

let _50_1121 = (encode_exp body envbody)
in (match (_50_1121) with
| (body, decls') -> begin
(

let key_body = (let _140_784 = (let _140_783 = (let _140_782 = (let _140_781 = (FStar_ToSMT_Term.mk_and_l guards)
in (_140_781, body))
in (FStar_ToSMT_Term.mkImp _140_782))
in ([], vars, _140_783))
in (FStar_ToSMT_Term.mkForall _140_784))
in (

let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (

let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _50_1127, _50_1129) -> begin
(let _140_787 = (let _140_786 = (let _140_785 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _140_785))
in (FStar_ToSMT_Term.mkApp _140_786))
in (_140_787, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
(t, [])
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let fsym = (varops.fresh "Exp_abs")
in (

let fdecl = FStar_ToSMT_Term.DeclFun ((fsym, cvar_sorts, FStar_ToSMT_Term.Term_sort, None))
in (

let f = (let _140_789 = (let _140_788 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _140_788))
in (FStar_ToSMT_Term.mkApp _140_789))
in (

let app = (mk_ApplyE f vars)
in (

let _50_1143 = (encode_typ_pred None tfun env f)
in (match (_50_1143) with
| (f_has_t, decls'') -> begin
(

let typing_f = (let _140_791 = (let _140_790 = (FStar_ToSMT_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_140_790, Some ((Prims.strcat fsym " typing"))))
in FStar_ToSMT_Term.Assume (_140_791))
in (

let interp_f = (let _140_798 = (let _140_797 = (let _140_796 = (let _140_795 = (let _140_794 = (let _140_793 = (FStar_ToSMT_Term.mk_IsTyped app)
in (let _140_792 = (FStar_ToSMT_Term.mkEq (app, body))
in (_140_793, _140_792)))
in (FStar_ToSMT_Term.mkImp _140_794))
in (((app)::[])::[], (FStar_List.append vars cvars), _140_795))
in (FStar_ToSMT_Term.mkForall _140_796))
in (_140_797, Some ((Prims.strcat fsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_140_798))
in (

let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (

let _50_1147 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end)))))))
end)
end))))
end))
end))
end)
end
| _50_1150 -> begin
(FStar_All.failwith "Impossible")
end))
end
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (l, _50_1161); FStar_Absyn_Syntax.tk = _50_1158; FStar_Absyn_Syntax.pos = _50_1156; FStar_Absyn_Syntax.fvs = _50_1154; FStar_Absyn_Syntax.uvs = _50_1152}, ((FStar_Util.Inl (_50_1176), _50_1179))::((FStar_Util.Inr (v1), _50_1173))::((FStar_Util.Inr (v2), _50_1168))::[]) when (FStar_Ident.lid_equals l.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
(

let _50_1186 = (encode_exp v1 env)
in (match (_50_1186) with
| (v1, decls1) -> begin
(

let _50_1189 = (encode_exp v2 env)
in (match (_50_1189) with
| (v2, decls2) -> begin
(let _140_799 = (FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_140_799, (FStar_List.append decls1 decls2)))
end))
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_50_1199); FStar_Absyn_Syntax.tk = _50_1197; FStar_Absyn_Syntax.pos = _50_1195; FStar_Absyn_Syntax.fvs = _50_1193; FStar_Absyn_Syntax.uvs = _50_1191}, _50_1203) -> begin
(let _140_800 = (whnf_e env e)
in (encode_exp _140_800 env))
end
| FStar_Absyn_Syntax.Exp_app (head, args_e) -> begin
(

let _50_1212 = (encode_args args_e env)
in (match (_50_1212) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _50_1217 = (encode_exp head env)
in (match (_50_1217) with
| (head, decls') -> begin
(

let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(

let _50_1226 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_50_1226) with
| (formals, rest) -> begin
(

let subst = (FStar_Absyn_Util.formals_for_actuals formals args_e)
in (

let ty = (let _140_803 = (FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (FStar_Absyn_Syntax.ktype)) e0.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _140_803 (FStar_Absyn_Util.subst_typ subst)))
in (

let _50_1231 = (encode_typ_pred None ty env app_tm)
in (match (_50_1231) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_ToSMT_Term.free_variables has_type)
in (

let e_typing = (let _140_805 = (let _140_804 = (FStar_ToSMT_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_140_804, None))
in FStar_ToSMT_Term.Assume (_140_805))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _50_1238 = (lookup_free_var_sym env fv)
in (match (_50_1238) with
| (fname, fuel_args) -> begin
(

let tm = (let _140_811 = (let _140_810 = (let _140_809 = (FStar_List.map (fun _50_11 -> (match (_50_11) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (FStar_List.append fuel_args _140_809))
in (fname, _140_810))
in (FStar_ToSMT_Term.mkApp' _140_811))
in (tm, decls))
end)))
in (

let head = (FStar_Absyn_Util.compress_exp head)
in (

let _50_1245 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("186"))) then begin
(let _140_813 = (FStar_Absyn_Print.exp_to_string head)
in (let _140_812 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.print2 "Recomputing type for %s\nFull term is %s\n" _140_813 _140_812)))
end else begin
()
end
in (

let head_type = (let _140_816 = (let _140_815 = (let _140_814 = (FStar_Tc_Recheck.recompute_typ head)
in (FStar_Absyn_Util.unrefine _140_814))
in (whnf env _140_815))
in (FStar_All.pipe_left FStar_Absyn_Util.unrefine _140_816))
in (

let _50_1248 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _140_819 = (FStar_Absyn_Print.exp_to_string head)
in (let _140_818 = (FStar_Absyn_Print.tag_of_exp head)
in (let _140_817 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.print3 "Recomputed type of head %s (%s) to be %s\n" _140_819 _140_818 _140_817))))
end else begin
()
end
in (match ((FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _140_823 = (let _140_822 = (FStar_Range.string_of_range e0.FStar_Absyn_Syntax.pos)
in (let _140_821 = (FStar_Absyn_Print.exp_to_string e0)
in (let _140_820 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.format3 "(%s) term is %s; head type is %s\n" _140_822 _140_821 _140_820))))
in (FStar_All.failwith _140_823))
end
| Some (formals, c) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _50_1257) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _50_1261 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some ((formals, c))))
end else begin
(encode_partial_app None)
end
end)
end)))))))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_50_1270); FStar_Absyn_Syntax.lbtyp = _50_1268; FStar_Absyn_Syntax.lbeff = _50_1266; FStar_Absyn_Syntax.lbdef = _50_1264})::[]), _50_1276) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Absyn_Syntax.Exp_let ((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = t1; FStar_Absyn_Syntax.lbeff = _50_1282; FStar_Absyn_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _50_1294 = (encode_exp e1 env)
in (match (_50_1294) with
| (ee1, decls1) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _50_1298 = (encode_exp e2 env')
in (match (_50_1298) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let (_50_1300) -> begin
(

let _50_1302 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_ToSMT_Term.DeclFun ((e, [], FStar_ToSMT_Term.Term_sort, None))
in (let _140_824 = (FStar_ToSMT_Term.mkFreeV (e, FStar_ToSMT_Term.Term_sort))
in (_140_824, (decl_e)::[])))))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(

let _50_1312 = (encode_exp e env)
in (match (_50_1312) with
| (scr, decls) -> begin
(

let _50_1352 = (FStar_List.fold_right (fun _50_1316 _50_1319 -> (match ((_50_1316, _50_1319)) with
| ((p, w, br), (else_case, decls)) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _50_1323 _50_1326 -> (match ((_50_1323, _50_1326)) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _50_1332 -> (match (_50_1332) with
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

let _50_1346 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(

let _50_1343 = (encode_exp w env)
in (match (_50_1343) with
| (w, decls2) -> begin
(let _140_835 = (let _140_834 = (let _140_833 = (let _140_832 = (let _140_831 = (FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
in (w, _140_831))
in (FStar_ToSMT_Term.mkEq _140_832))
in (guard, _140_833))
in (FStar_ToSMT_Term.mkAnd _140_834))
in (_140_835, decls2))
end))
end)
in (match (_50_1346) with
| (guard, decls2) -> begin
(

let _50_1349 = (encode_exp br env)
in (match (_50_1349) with
| (br, decls3) -> begin
(let _140_836 = (FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_140_836, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end)) pats (FStar_ToSMT_Term.mk_Term_unit, decls))
in (match (_50_1352) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (_50_1354) -> begin
(let _140_839 = (let _140_838 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _140_837 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "(%s): Impossible: encode_exp got %s" _140_838 _140_837)))
in (FStar_All.failwith _140_839))
end))))
and encode_pat : env_t  ->  FStar_Absyn_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _50_1361 -> begin
(let _140_842 = (encode_one_pat env pat)
in (_140_842)::[])
end))
and encode_one_pat : env_t  ->  FStar_Absyn_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _50_1364 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _140_845 = (FStar_Absyn_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _140_845))
end else begin
()
end
in (

let _50_1368 = (FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_50_1368) with
| (vars, pat_exp_or_typ) -> begin
(

let _50_1389 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _50_1371 v -> (match (_50_1371) with
| (env, vars) -> begin
(match (v) with
| FStar_Util.Inl (a) -> begin
(

let _50_1379 = (gen_typ_var env a.FStar_Absyn_Syntax.v)
in (match (_50_1379) with
| (aa, _50_1377, env) -> begin
(env, ((v, (aa, FStar_ToSMT_Term.Type_sort)))::vars)
end))
end
| FStar_Util.Inr (x) -> begin
(

let _50_1386 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_50_1386) with
| (xx, _50_1384, env) -> begin
(env, ((v, (xx, FStar_ToSMT_Term.Term_sort)))::vars)
end))
end)
end)) (env, [])))
in (match (_50_1389) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_50_1394) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
FStar_ToSMT_Term.mkTrue
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _140_853 = (let _140_852 = (encode_const c)
in (scrutinee, _140_852))
in (FStar_ToSMT_Term.mkEq _140_853))
end
| FStar_Absyn_Syntax.Pat_cons (f, _50_1418, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Absyn_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _50_1427 -> (match (_50_1427) with
| (arg, _50_1426) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _140_856 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _140_856)))
end))))
in (FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_50_1434) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _)) | (FStar_Absyn_Syntax.Pat_var (x)) | (FStar_Absyn_Syntax.Pat_wild (x)) -> begin
((FStar_Util.Inr (x), scrutinee))::[]
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _)) | (FStar_Absyn_Syntax.Pat_tvar (a)) | (FStar_Absyn_Syntax.Pat_twild (a)) -> begin
((FStar_Util.Inl (a), scrutinee))::[]
end
| FStar_Absyn_Syntax.Pat_constant (_50_1451) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_cons (f, _50_1455, args) -> begin
(let _140_864 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _50_1463 -> (match (_50_1463) with
| (arg, _50_1462) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _140_863 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _140_863)))
end))))
in (FStar_All.pipe_right _140_864 FStar_List.flatten))
end))
in (

let pat_term = (fun _50_1466 -> (match (()) with
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
in (env, pattern)))))
end))
end))))
and encode_args : FStar_Absyn_Syntax.args  ->  env_t  ->  ((FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list * FStar_ToSMT_Term.decls_t) = (fun l env -> (

let _50_1496 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _50_1476 x -> (match (_50_1476) with
| (tms, decls) -> begin
(match (x) with
| (FStar_Util.Inl (t), _50_1481) -> begin
(

let _50_1485 = (encode_typ_term t env)
in (match (_50_1485) with
| (t, decls') -> begin
((FStar_Util.Inl (t))::tms, (FStar_List.append decls decls'))
end))
end
| (FStar_Util.Inr (e), _50_1489) -> begin
(

let _50_1493 = (encode_exp e env)
in (match (_50_1493) with
| (t, decls') -> begin
((FStar_Util.Inr (t))::tms, (FStar_List.append decls decls'))
end))
end)
end)) ([], [])))
in (match (_50_1496) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_formula : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun phi env -> (

let _50_1502 = (encode_formula_with_labels phi env)
in (match (_50_1502) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _50_1505 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.exp Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun induction_on new_pats t env -> (

let rec list_elements = (fun e -> (match ((let _140_879 = (FStar_Absyn_Util.unmeta_exp e)
in _140_879.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_1522); FStar_Absyn_Syntax.tk = _50_1519; FStar_Absyn_Syntax.pos = _50_1517; FStar_Absyn_Syntax.fvs = _50_1515; FStar_Absyn_Syntax.uvs = _50_1513}, _50_1527) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.nil_lid) -> begin
[]
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_1540); FStar_Absyn_Syntax.tk = _50_1537; FStar_Absyn_Syntax.pos = _50_1535; FStar_Absyn_Syntax.fvs = _50_1533; FStar_Absyn_Syntax.uvs = _50_1531}, (_50_1555)::((FStar_Util.Inr (hd), _50_1552))::((FStar_Util.Inr (tl), _50_1547))::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(let _140_880 = (list_elements tl)
in (hd)::_140_880)
end
| _50_1560 -> begin
(

let _50_1561 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (

let v_or_t_pat = (fun p -> (match ((let _140_883 = (FStar_Absyn_Util.unmeta_exp p)
in _140_883.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_1575); FStar_Absyn_Syntax.tk = _50_1572; FStar_Absyn_Syntax.pos = _50_1570; FStar_Absyn_Syntax.fvs = _50_1568; FStar_Absyn_Syntax.uvs = _50_1566}, ((FStar_Util.Inl (_50_1585), _50_1588))::((FStar_Util.Inr (e), _50_1582))::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpat_lid) -> begin
(FStar_Absyn_Syntax.varg e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_1603); FStar_Absyn_Syntax.tk = _50_1600; FStar_Absyn_Syntax.pos = _50_1598; FStar_Absyn_Syntax.fvs = _50_1596; FStar_Absyn_Syntax.uvs = _50_1594}, ((FStar_Util.Inl (t), _50_1610))::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatT_lid) -> begin
(FStar_Absyn_Syntax.targ t)
end
| _50_1616 -> begin
(FStar_All.failwith "Unexpected pattern term")
end))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (match (elts) with
| ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_1638); FStar_Absyn_Syntax.tk = _50_1635; FStar_Absyn_Syntax.pos = _50_1633; FStar_Absyn_Syntax.fvs = _50_1631; FStar_Absyn_Syntax.uvs = _50_1629}, ((FStar_Util.Inr (e), _50_1645))::[]); FStar_Absyn_Syntax.tk = _50_1627; FStar_Absyn_Syntax.pos = _50_1625; FStar_Absyn_Syntax.fvs = _50_1623; FStar_Absyn_Syntax.uvs = _50_1621})::[] when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatOr_lid) -> begin
(let _140_888 = (list_elements e)
in (FStar_All.pipe_right _140_888 (FStar_List.map (fun branch -> (let _140_887 = (list_elements branch)
in (FStar_All.pipe_right _140_887 (FStar_List.map v_or_t_pat)))))))
end
| _50_1654 -> begin
(let _140_889 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_140_889)::[])
end)))
in (

let _50_1697 = (match ((let _140_890 = (FStar_Absyn_Util.compress_typ t)
in _140_890.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (ct); FStar_Absyn_Syntax.tk = _50_1663; FStar_Absyn_Syntax.pos = _50_1661; FStar_Absyn_Syntax.fvs = _50_1659; FStar_Absyn_Syntax.uvs = _50_1657}) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| ((FStar_Util.Inl (pre), _50_1682))::((FStar_Util.Inl (post), _50_1677))::((FStar_Util.Inr (pats), _50_1672))::[] -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _140_891 = (lemma_pats pats')
in (binders, pre, post, _140_891)))
end
| _50_1690 -> begin
(FStar_All.failwith "impos")
end)
end
| _50_1692 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_50_1697) with
| (binders, pre, post, patterns) -> begin
(

let _50_1704 = (encode_binders None binders env)
in (match (_50_1704) with
| (vars, guards, env, decls, _50_1703) -> begin
(

let _50_1724 = (let _140_895 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _50_1721 = (let _140_894 = (FStar_All.pipe_right branch (FStar_List.map (fun _50_12 -> (match (_50_12) with
| (FStar_Util.Inl (t), _50_1710) -> begin
(encode_formula t env)
end
| (FStar_Util.Inr (e), _50_1715) -> begin
(encode_exp e (

let _50_1717 = env
in {bindings = _50_1717.bindings; depth = _50_1717.depth; tcenv = _50_1717.tcenv; warn = _50_1717.warn; cache = _50_1717.cache; nolabels = _50_1717.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _50_1717.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _140_894 FStar_List.unzip))
in (match (_50_1721) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _140_895 FStar_List.unzip))
in (match (_50_1724) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _140_898 = (let _140_897 = (FStar_ToSMT_Term.mkFreeV l)
in (FStar_ToSMT_Term.mk_Precedes _140_897 e))
in (_140_898)::p))))
end
| _50_1734 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _140_904 = (FStar_ToSMT_Term.mk_Precedes tl e)
in (_140_904)::p))))
end
| ((x, FStar_ToSMT_Term.Term_sort))::vars -> begin
(let _140_906 = (let _140_905 = (FStar_ToSMT_Term.mkFreeV (x, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_LexCons _140_905 tl))
in (aux _140_906 vars))
end
| _50_1746 -> begin
pats
end))
in (let _140_907 = (FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", FStar_ToSMT_Term.Term_sort))
in (aux _140_907 vars)))
end)
end)
in (

let env = (

let _50_1748 = env
in {bindings = _50_1748.bindings; depth = _50_1748.depth; tcenv = _50_1748.tcenv; warn = _50_1748.warn; cache = _50_1748.cache; nolabels = true; use_zfuel_name = _50_1748.use_zfuel_name; encode_non_total_function_typ = _50_1748.encode_non_total_function_typ})
in (

let _50_1753 = (let _140_908 = (FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _140_908 env))
in (match (_50_1753) with
| (pre, decls'') -> begin
(

let _50_1756 = (let _140_909 = (FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _140_909 env))
in (match (_50_1756) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _140_914 = (let _140_913 = (let _140_912 = (let _140_911 = (let _140_910 = (FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_140_910, post))
in (FStar_ToSMT_Term.mkImp _140_911))
in (pats, vars, _140_912))
in (FStar_ToSMT_Term.mkForall _140_913))
in (_140_914, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula_with_labels : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * labels * FStar_ToSMT_Term.decls_t) = (fun phi env -> (

let enc = (fun f l -> (

let _50_1777 = (FStar_Util.fold_map (fun decls x -> (match ((Prims.fst x)) with
| FStar_Util.Inl (t) -> begin
(

let _50_1769 = (encode_typ_term t env)
in (match (_50_1769) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))
end
| FStar_Util.Inr (e) -> begin
(

let _50_1774 = (encode_exp e env)
in (match (_50_1774) with
| (e, decls') -> begin
((FStar_List.append decls decls'), e)
end))
end)) [] l)
in (match (_50_1777) with
| (decls, args) -> begin
(let _140_932 = (f args)
in (_140_932, [], decls))
end)))
in (

let enc_prop_c = (fun f l -> (

let _50_1797 = (FStar_List.fold_right (fun t _50_1785 -> (match (_50_1785) with
| (phis, labs, decls) -> begin
(match ((Prims.fst t)) with
| FStar_Util.Inl (t) -> begin
(

let _50_1791 = (encode_formula_with_labels t env)
in (match (_50_1791) with
| (phi, labs', decls') -> begin
((phi)::phis, (FStar_List.append labs' labs), (FStar_List.append decls' decls))
end))
end
| _50_1793 -> begin
(FStar_All.failwith "Expected a formula")
end)
end)) l ([], [], []))
in (match (_50_1797) with
| (phis, labs, decls) -> begin
(let _140_948 = (f phis)
in (_140_948, labs, decls))
end)))
in (

let const_op = (fun f _50_1800 -> (f, [], []))
in (

let un_op = (fun f l -> (let _140_962 = (FStar_List.hd l)
in (FStar_All.pipe_left f _140_962)))
in (

let bin_op = (fun f _50_13 -> (match (_50_13) with
| (t1)::(t2)::[] -> begin
(f (t1, t2))
end
| _50_1811 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let eq_op = (fun _50_14 -> (match (_50_14) with
| (_50_1819)::(_50_1817)::(e1)::(e2)::[] -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) l)
end))
in (

let mk_imp = (fun _50_15 -> (match (_50_15) with
| ((FStar_Util.Inl (lhs), _50_1832))::((FStar_Util.Inl (rhs), _50_1827))::[] -> begin
(

let _50_1838 = (encode_formula_with_labels rhs env)
in (match (_50_1838) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _50_1841) -> begin
(l1, labs1, decls1)
end
| _50_1845 -> begin
(

let _50_1849 = (encode_formula_with_labels lhs env)
in (match (_50_1849) with
| (l2, labs2, decls2) -> begin
(let _140_976 = (FStar_ToSMT_Term.mkImp (l2, l1))
in (_140_976, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _50_1851 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun _50_16 -> (match (_50_16) with
| ((FStar_Util.Inl (guard), _50_1867))::((FStar_Util.Inl (_then), _50_1862))::((FStar_Util.Inl (_else), _50_1857))::[] -> begin
(

let _50_1873 = (encode_formula_with_labels guard env)
in (match (_50_1873) with
| (g, labs1, decls1) -> begin
(

let _50_1877 = (encode_formula_with_labels _then env)
in (match (_50_1877) with
| (t, labs2, decls2) -> begin
(

let _50_1881 = (encode_formula_with_labels _else env)
in (match (_50_1881) with
| (e, labs3, decls3) -> begin
(

let res = (FStar_ToSMT_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append labs1 labs2) labs3), (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _50_1884 -> begin
(FStar_All.failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _140_988 = (FStar_List.map FStar_ToSMT_Term.unboxInt l)
in (f _140_988)))
in (

let connectives = (let _140_1049 = (let _140_997 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkAnd))
in (FStar_Absyn_Const.and_lid, _140_997))
in (let _140_1048 = (let _140_1047 = (let _140_1003 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkOr))
in (FStar_Absyn_Const.or_lid, _140_1003))
in (let _140_1046 = (let _140_1045 = (let _140_1044 = (let _140_1012 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkIff))
in (FStar_Absyn_Const.iff_lid, _140_1012))
in (let _140_1043 = (let _140_1042 = (let _140_1041 = (let _140_1021 = (FStar_All.pipe_left enc_prop_c (un_op FStar_ToSMT_Term.mkNot))
in (FStar_Absyn_Const.not_lid, _140_1021))
in (let _140_1040 = (let _140_1039 = (let _140_1027 = (FStar_All.pipe_left enc (bin_op FStar_ToSMT_Term.mkEq))
in (FStar_Absyn_Const.eqT_lid, _140_1027))
in (_140_1039)::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op FStar_ToSMT_Term.mkTrue)))::((FStar_Absyn_Const.false_lid, (const_op FStar_ToSMT_Term.mkFalse)))::[])
in (_140_1041)::_140_1040))
in ((FStar_Absyn_Const.ite_lid, mk_ite))::_140_1042)
in (_140_1044)::_140_1043))
in ((FStar_Absyn_Const.imp_lid, mk_imp))::_140_1045)
in (_140_1047)::_140_1046))
in (_140_1049)::_140_1048))
in (

let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (phi', msg, r, b)) -> begin
(

let _50_1902 = (encode_formula_with_labels phi' env)
in (match (_50_1902) with
| (phi, labs, decls) -> begin
if env.nolabels then begin
(phi, [], decls)
end else begin
(

let lvar = (let _140_1052 = (varops.fresh "label")
in (_140_1052, FStar_ToSMT_Term.Bool_sort))
in (

let lterm = (FStar_ToSMT_Term.mkFreeV lvar)
in (

let lphi = (FStar_ToSMT_Term.mkOr (lterm, phi))
in (lphi, ((lvar, msg, r))::labs, decls))))
end
end))
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _50_1913; FStar_Absyn_Syntax.pos = _50_1911; FStar_Absyn_Syntax.fvs = _50_1909; FStar_Absyn_Syntax.uvs = _50_1907}, (_50_1928)::((FStar_Util.Inr (l), _50_1925))::((FStar_Util.Inl (phi), _50_1920))::[]) when (FStar_Ident.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_IH) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(

let _50_1934 = (encode_exp l env)
in (match (_50_1934) with
| (e, decls) -> begin
(

let _50_1937 = (encode_function_type_as_formula (Some (e)) None phi env)
in (match (_50_1937) with
| (f, decls') -> begin
(f, [], (FStar_List.append decls decls'))
end))
end))
end else begin
(FStar_ToSMT_Term.mkTrue, [], [])
end
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _50_1945; FStar_Absyn_Syntax.pos = _50_1943; FStar_Absyn_Syntax.fvs = _50_1941; FStar_Absyn_Syntax.uvs = _50_1939}, (_50_1957)::((FStar_Util.Inl (phi), _50_1953))::tl) when (FStar_Ident.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_lem) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(

let pat = (match (tl) with
| [] -> begin
None
end
| ((FStar_Util.Inr (pat), _50_1965))::[] -> begin
Some (pat)
end)
in (

let _50_1971 = (encode_function_type_as_formula None pat phi env)
in (match (_50_1971) with
| (f, decls) -> begin
(f, [], decls)
end)))
end else begin
(FStar_ToSMT_Term.mkTrue, [], [])
end
end
| _50_1973 -> begin
(

let _50_1976 = (encode_typ_term phi env)
in (match (_50_1976) with
| (tt, decls) -> begin
(let _140_1053 = (FStar_ToSMT_Term.mk_Valid tt)
in (_140_1053, [], decls))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _50_1988 = (encode_binders None bs env)
in (match (_50_1988) with
| (vars, guards, env, decls, _50_1987) -> begin
(

let _50_2008 = (let _140_1065 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _50_2005 = (let _140_1064 = (FStar_All.pipe_right p (FStar_List.map (fun _50_17 -> (match (_50_17) with
| (FStar_Util.Inl (t), _50_1994) -> begin
(encode_typ_term t env)
end
| (FStar_Util.Inr (e), _50_1999) -> begin
(encode_exp e (

let _50_2001 = env
in {bindings = _50_2001.bindings; depth = _50_2001.depth; tcenv = _50_2001.tcenv; warn = _50_2001.warn; cache = _50_2001.cache; nolabels = _50_2001.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _50_2001.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _140_1064 FStar_List.unzip))
in (match (_50_2005) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _140_1065 FStar_List.unzip))
in (match (_50_2008) with
| (pats, decls') -> begin
(

let _50_2012 = (encode_formula_with_labels body env)
in (match (_50_2012) with
| (body, labs, decls'') -> begin
(let _140_1066 = (FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _140_1066, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (

let _50_2013 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _140_1067 = (FStar_Absyn_Print.formula_to_string phi)
in (FStar_Util.print1 ">>>> Destructing as formula ... %s\n" _140_1067))
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
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _50_2025 -> (match (_50_2025) with
| (l, _50_2024) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_50_2028, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, pats, body)) -> begin
(

let _50_2038 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _140_1084 = (FStar_All.pipe_right vars (FStar_Absyn_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _140_1084))
end else begin
()
end
in (

let _50_2046 = (encode_q_body env vars pats body)
in (match (_50_2046) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _140_1087 = (let _140_1086 = (let _140_1085 = (FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _140_1085))
in (FStar_ToSMT_Term.mkForall _140_1086))
in (_140_1087, labs, decls))
end)))
end
| Some (FStar_Absyn_Util.QEx (vars, pats, body)) -> begin
(

let _50_2059 = (encode_q_body env vars pats body)
in (match (_50_2059) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _140_1090 = (let _140_1089 = (let _140_1088 = (FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _140_1088))
in (FStar_ToSMT_Term.mkExists _140_1089))
in (_140_1090, labs, decls))
end))
end))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _50_2065 = (fresh_fvar "a" FStar_ToSMT_Term.Type_sort)
in (match (_50_2065) with
| (asym, a) -> begin
(

let _50_2068 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_50_2068) with
| (xsym, x) -> begin
(

let _50_2071 = (fresh_fvar "y" FStar_ToSMT_Term.Term_sort)
in (match (_50_2071) with
| (ysym, y) -> begin
(

let deffun = (fun vars body x -> (let _140_1125 = (let _140_1124 = (let _140_1123 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _140_1122 = (FStar_ToSMT_Term.abstr vars body)
in (x, _140_1123, FStar_ToSMT_Term.Term_sort, _140_1122, None)))
in FStar_ToSMT_Term.DefineFun (_140_1124))
in (_140_1125)::[]))
in (

let quant = (fun vars body x -> (

let t1 = (let _140_1137 = (let _140_1136 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (x, _140_1136))
in (FStar_ToSMT_Term.mkApp _140_1137))
in (

let vname_decl = (let _140_1139 = (let _140_1138 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _140_1138, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_140_1139))
in (let _140_1145 = (let _140_1144 = (let _140_1143 = (let _140_1142 = (let _140_1141 = (let _140_1140 = (FStar_ToSMT_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _140_1140))
in (FStar_ToSMT_Term.mkForall _140_1141))
in (_140_1142, None))
in FStar_ToSMT_Term.Assume (_140_1143))
in (_140_1144)::[])
in (vname_decl)::_140_1145))))
in (

let def_or_quant = (fun vars body x -> if (FStar_Options.inline_arith ()) then begin
(deffun vars body x)
end else begin
(quant vars body x)
end)
in (

let axy = ((asym, FStar_ToSMT_Term.Type_sort))::((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (

let xy = ((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (

let qx = ((xsym, FStar_ToSMT_Term.Term_sort))::[]
in (

let prims = (let _140_1311 = (let _140_1160 = (let _140_1159 = (let _140_1158 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _140_1158))
in (def_or_quant axy _140_1159))
in (FStar_Absyn_Const.op_Eq, _140_1160))
in (let _140_1310 = (let _140_1309 = (let _140_1167 = (let _140_1166 = (let _140_1165 = (let _140_1164 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_ToSMT_Term.mkNot _140_1164))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _140_1165))
in (def_or_quant axy _140_1166))
in (FStar_Absyn_Const.op_notEq, _140_1167))
in (let _140_1308 = (let _140_1307 = (let _140_1176 = (let _140_1175 = (let _140_1174 = (let _140_1173 = (let _140_1172 = (FStar_ToSMT_Term.unboxInt x)
in (let _140_1171 = (FStar_ToSMT_Term.unboxInt y)
in (_140_1172, _140_1171)))
in (FStar_ToSMT_Term.mkLT _140_1173))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _140_1174))
in (def_or_quant xy _140_1175))
in (FStar_Absyn_Const.op_LT, _140_1176))
in (let _140_1306 = (let _140_1305 = (let _140_1185 = (let _140_1184 = (let _140_1183 = (let _140_1182 = (let _140_1181 = (FStar_ToSMT_Term.unboxInt x)
in (let _140_1180 = (FStar_ToSMT_Term.unboxInt y)
in (_140_1181, _140_1180)))
in (FStar_ToSMT_Term.mkLTE _140_1182))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _140_1183))
in (def_or_quant xy _140_1184))
in (FStar_Absyn_Const.op_LTE, _140_1185))
in (let _140_1304 = (let _140_1303 = (let _140_1194 = (let _140_1193 = (let _140_1192 = (let _140_1191 = (let _140_1190 = (FStar_ToSMT_Term.unboxInt x)
in (let _140_1189 = (FStar_ToSMT_Term.unboxInt y)
in (_140_1190, _140_1189)))
in (FStar_ToSMT_Term.mkGT _140_1191))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _140_1192))
in (def_or_quant xy _140_1193))
in (FStar_Absyn_Const.op_GT, _140_1194))
in (let _140_1302 = (let _140_1301 = (let _140_1203 = (let _140_1202 = (let _140_1201 = (let _140_1200 = (let _140_1199 = (FStar_ToSMT_Term.unboxInt x)
in (let _140_1198 = (FStar_ToSMT_Term.unboxInt y)
in (_140_1199, _140_1198)))
in (FStar_ToSMT_Term.mkGTE _140_1200))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _140_1201))
in (def_or_quant xy _140_1202))
in (FStar_Absyn_Const.op_GTE, _140_1203))
in (let _140_1300 = (let _140_1299 = (let _140_1212 = (let _140_1211 = (let _140_1210 = (let _140_1209 = (let _140_1208 = (FStar_ToSMT_Term.unboxInt x)
in (let _140_1207 = (FStar_ToSMT_Term.unboxInt y)
in (_140_1208, _140_1207)))
in (FStar_ToSMT_Term.mkSub _140_1209))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _140_1210))
in (def_or_quant xy _140_1211))
in (FStar_Absyn_Const.op_Subtraction, _140_1212))
in (let _140_1298 = (let _140_1297 = (let _140_1219 = (let _140_1218 = (let _140_1217 = (let _140_1216 = (FStar_ToSMT_Term.unboxInt x)
in (FStar_ToSMT_Term.mkMinus _140_1216))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _140_1217))
in (def_or_quant qx _140_1218))
in (FStar_Absyn_Const.op_Minus, _140_1219))
in (let _140_1296 = (let _140_1295 = (let _140_1228 = (let _140_1227 = (let _140_1226 = (let _140_1225 = (let _140_1224 = (FStar_ToSMT_Term.unboxInt x)
in (let _140_1223 = (FStar_ToSMT_Term.unboxInt y)
in (_140_1224, _140_1223)))
in (FStar_ToSMT_Term.mkAdd _140_1225))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _140_1226))
in (def_or_quant xy _140_1227))
in (FStar_Absyn_Const.op_Addition, _140_1228))
in (let _140_1294 = (let _140_1293 = (let _140_1237 = (let _140_1236 = (let _140_1235 = (let _140_1234 = (let _140_1233 = (FStar_ToSMT_Term.unboxInt x)
in (let _140_1232 = (FStar_ToSMT_Term.unboxInt y)
in (_140_1233, _140_1232)))
in (FStar_ToSMT_Term.mkMul _140_1234))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _140_1235))
in (def_or_quant xy _140_1236))
in (FStar_Absyn_Const.op_Multiply, _140_1237))
in (let _140_1292 = (let _140_1291 = (let _140_1246 = (let _140_1245 = (let _140_1244 = (let _140_1243 = (let _140_1242 = (FStar_ToSMT_Term.unboxInt x)
in (let _140_1241 = (FStar_ToSMT_Term.unboxInt y)
in (_140_1242, _140_1241)))
in (FStar_ToSMT_Term.mkDiv _140_1243))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _140_1244))
in (def_or_quant xy _140_1245))
in (FStar_Absyn_Const.op_Division, _140_1246))
in (let _140_1290 = (let _140_1289 = (let _140_1255 = (let _140_1254 = (let _140_1253 = (let _140_1252 = (let _140_1251 = (FStar_ToSMT_Term.unboxInt x)
in (let _140_1250 = (FStar_ToSMT_Term.unboxInt y)
in (_140_1251, _140_1250)))
in (FStar_ToSMT_Term.mkMod _140_1252))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _140_1253))
in (def_or_quant xy _140_1254))
in (FStar_Absyn_Const.op_Modulus, _140_1255))
in (let _140_1288 = (let _140_1287 = (let _140_1264 = (let _140_1263 = (let _140_1262 = (let _140_1261 = (let _140_1260 = (FStar_ToSMT_Term.unboxBool x)
in (let _140_1259 = (FStar_ToSMT_Term.unboxBool y)
in (_140_1260, _140_1259)))
in (FStar_ToSMT_Term.mkAnd _140_1261))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _140_1262))
in (def_or_quant xy _140_1263))
in (FStar_Absyn_Const.op_And, _140_1264))
in (let _140_1286 = (let _140_1285 = (let _140_1273 = (let _140_1272 = (let _140_1271 = (let _140_1270 = (let _140_1269 = (FStar_ToSMT_Term.unboxBool x)
in (let _140_1268 = (FStar_ToSMT_Term.unboxBool y)
in (_140_1269, _140_1268)))
in (FStar_ToSMT_Term.mkOr _140_1270))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _140_1271))
in (def_or_quant xy _140_1272))
in (FStar_Absyn_Const.op_Or, _140_1273))
in (let _140_1284 = (let _140_1283 = (let _140_1280 = (let _140_1279 = (let _140_1278 = (let _140_1277 = (FStar_ToSMT_Term.unboxBool x)
in (FStar_ToSMT_Term.mkNot _140_1277))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _140_1278))
in (def_or_quant qx _140_1279))
in (FStar_Absyn_Const.op_Negation, _140_1280))
in (_140_1283)::[])
in (_140_1285)::_140_1284))
in (_140_1287)::_140_1286))
in (_140_1289)::_140_1288))
in (_140_1291)::_140_1290))
in (_140_1293)::_140_1292))
in (_140_1295)::_140_1294))
in (_140_1297)::_140_1296))
in (_140_1299)::_140_1298))
in (_140_1301)::_140_1300))
in (_140_1303)::_140_1302))
in (_140_1305)::_140_1304))
in (_140_1307)::_140_1306))
in (_140_1309)::_140_1308))
in (_140_1311)::_140_1310))
in (

let mk = (fun l v -> (let _140_1343 = (FStar_All.pipe_right prims (FStar_List.filter (fun _50_2095 -> (match (_50_2095) with
| (l', _50_2094) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _140_1343 (FStar_List.collect (fun _50_2099 -> (match (_50_2099) with
| (_50_2097, b) -> begin
(b v)
end))))))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _50_2105 -> (match (_50_2105) with
| (l', _50_2104) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))))
end))
end))
end))


let primitive_type_axioms : FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.decl Prims.list = (

let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let yy = ("y", FStar_ToSMT_Term.Term_sort)
in (

let y = (FStar_ToSMT_Term.mkFreeV yy)
in (

let mk_unit = (fun _50_2111 tt -> (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let _140_1375 = (let _140_1366 = (let _140_1365 = (FStar_ToSMT_Term.mk_HasType FStar_ToSMT_Term.mk_Term_unit tt)
in (_140_1365, Some ("unit typing")))
in FStar_ToSMT_Term.Assume (_140_1366))
in (let _140_1374 = (let _140_1373 = (let _140_1372 = (let _140_1371 = (let _140_1370 = (let _140_1369 = (let _140_1368 = (let _140_1367 = (FStar_ToSMT_Term.mkEq (x, FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _140_1367))
in (FStar_ToSMT_Term.mkImp _140_1368))
in (((typing_pred)::[])::[], (xx)::[], _140_1369))
in (mkForall_fuel _140_1370))
in (_140_1371, Some ("unit inversion")))
in FStar_ToSMT_Term.Assume (_140_1372))
in (_140_1373)::[])
in (_140_1375)::_140_1374))))
in (

let mk_bool = (fun _50_2116 tt -> (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (

let bb = ("b", FStar_ToSMT_Term.Bool_sort)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _140_1396 = (let _140_1385 = (let _140_1384 = (let _140_1383 = (let _140_1382 = (let _140_1381 = (let _140_1380 = (FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _140_1380))
in (FStar_ToSMT_Term.mkImp _140_1381))
in (((typing_pred)::[])::[], (xx)::[], _140_1382))
in (mkForall_fuel _140_1383))
in (_140_1384, Some ("bool inversion")))
in FStar_ToSMT_Term.Assume (_140_1385))
in (let _140_1395 = (let _140_1394 = (let _140_1393 = (let _140_1392 = (let _140_1391 = (let _140_1390 = (let _140_1387 = (let _140_1386 = (FStar_ToSMT_Term.boxBool b)
in (_140_1386)::[])
in (_140_1387)::[])
in (let _140_1389 = (let _140_1388 = (FStar_ToSMT_Term.boxBool b)
in (FStar_ToSMT_Term.mk_HasType _140_1388 tt))
in (_140_1390, (bb)::[], _140_1389)))
in (FStar_ToSMT_Term.mkForall _140_1391))
in (_140_1392, Some ("bool typing")))
in FStar_ToSMT_Term.Assume (_140_1393))
in (_140_1394)::[])
in (_140_1396)::_140_1395))))))
in (

let mk_int = (fun _50_2123 tt -> (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (

let typing_pred_y = (FStar_ToSMT_Term.mk_HasType y tt)
in (

let aa = ("a", FStar_ToSMT_Term.Int_sort)
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let bb = ("b", FStar_ToSMT_Term.Int_sort)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let precedes = (let _140_1408 = (let _140_1407 = (let _140_1406 = (let _140_1405 = (let _140_1404 = (let _140_1403 = (FStar_ToSMT_Term.boxInt a)
in (let _140_1402 = (let _140_1401 = (FStar_ToSMT_Term.boxInt b)
in (_140_1401)::[])
in (_140_1403)::_140_1402))
in (tt)::_140_1404)
in (tt)::_140_1405)
in ("Prims.Precedes", _140_1406))
in (FStar_ToSMT_Term.mkApp _140_1407))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _140_1408))
in (

let precedes_y_x = (let _140_1409 = (FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _140_1409))
in (let _140_1451 = (let _140_1415 = (let _140_1414 = (let _140_1413 = (let _140_1412 = (let _140_1411 = (let _140_1410 = (FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _140_1410))
in (FStar_ToSMT_Term.mkImp _140_1411))
in (((typing_pred)::[])::[], (xx)::[], _140_1412))
in (mkForall_fuel _140_1413))
in (_140_1414, Some ("int inversion")))
in FStar_ToSMT_Term.Assume (_140_1415))
in (let _140_1450 = (let _140_1449 = (let _140_1423 = (let _140_1422 = (let _140_1421 = (let _140_1420 = (let _140_1417 = (let _140_1416 = (FStar_ToSMT_Term.boxInt b)
in (_140_1416)::[])
in (_140_1417)::[])
in (let _140_1419 = (let _140_1418 = (FStar_ToSMT_Term.boxInt b)
in (FStar_ToSMT_Term.mk_HasType _140_1418 tt))
in (_140_1420, (bb)::[], _140_1419)))
in (FStar_ToSMT_Term.mkForall _140_1421))
in (_140_1422, Some ("int typing")))
in FStar_ToSMT_Term.Assume (_140_1423))
in (let _140_1448 = (let _140_1447 = (let _140_1446 = (let _140_1445 = (let _140_1444 = (let _140_1443 = (let _140_1442 = (let _140_1441 = (let _140_1440 = (let _140_1439 = (let _140_1438 = (let _140_1437 = (let _140_1426 = (let _140_1425 = (FStar_ToSMT_Term.unboxInt x)
in (let _140_1424 = (FStar_ToSMT_Term.mkInteger' 0)
in (_140_1425, _140_1424)))
in (FStar_ToSMT_Term.mkGT _140_1426))
in (let _140_1436 = (let _140_1435 = (let _140_1429 = (let _140_1428 = (FStar_ToSMT_Term.unboxInt y)
in (let _140_1427 = (FStar_ToSMT_Term.mkInteger' 0)
in (_140_1428, _140_1427)))
in (FStar_ToSMT_Term.mkGTE _140_1429))
in (let _140_1434 = (let _140_1433 = (let _140_1432 = (let _140_1431 = (FStar_ToSMT_Term.unboxInt y)
in (let _140_1430 = (FStar_ToSMT_Term.unboxInt x)
in (_140_1431, _140_1430)))
in (FStar_ToSMT_Term.mkLT _140_1432))
in (_140_1433)::[])
in (_140_1435)::_140_1434))
in (_140_1437)::_140_1436))
in (typing_pred_y)::_140_1438)
in (typing_pred)::_140_1439)
in (FStar_ToSMT_Term.mk_and_l _140_1440))
in (_140_1441, precedes_y_x))
in (FStar_ToSMT_Term.mkImp _140_1442))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _140_1443))
in (mkForall_fuel _140_1444))
in (_140_1445, Some ("well-founded ordering on nat (alt)")))
in FStar_ToSMT_Term.Assume (_140_1446))
in (_140_1447)::[])
in (_140_1449)::_140_1448))
in (_140_1451)::_140_1450)))))))))))
in (

let mk_int_alias = (fun _50_2135 tt -> (let _140_1460 = (let _140_1459 = (let _140_1458 = (let _140_1457 = (let _140_1456 = (FStar_ToSMT_Term.mkApp (FStar_Absyn_Const.int_lid.FStar_Ident.str, []))
in (tt, _140_1456))
in (FStar_ToSMT_Term.mkEq _140_1457))
in (_140_1458, Some ("mapping to int; for now")))
in FStar_ToSMT_Term.Assume (_140_1459))
in (_140_1460)::[]))
in (

let mk_str = (fun _50_2139 tt -> (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (

let bb = ("b", FStar_ToSMT_Term.String_sort)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _140_1481 = (let _140_1470 = (let _140_1469 = (let _140_1468 = (let _140_1467 = (let _140_1466 = (let _140_1465 = (FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _140_1465))
in (FStar_ToSMT_Term.mkImp _140_1466))
in (((typing_pred)::[])::[], (xx)::[], _140_1467))
in (mkForall_fuel _140_1468))
in (_140_1469, Some ("string inversion")))
in FStar_ToSMT_Term.Assume (_140_1470))
in (let _140_1480 = (let _140_1479 = (let _140_1478 = (let _140_1477 = (let _140_1476 = (let _140_1475 = (let _140_1472 = (let _140_1471 = (FStar_ToSMT_Term.boxString b)
in (_140_1471)::[])
in (_140_1472)::[])
in (let _140_1474 = (let _140_1473 = (FStar_ToSMT_Term.boxString b)
in (FStar_ToSMT_Term.mk_HasType _140_1473 tt))
in (_140_1475, (bb)::[], _140_1474)))
in (FStar_ToSMT_Term.mkForall _140_1476))
in (_140_1477, Some ("string typing")))
in FStar_ToSMT_Term.Assume (_140_1478))
in (_140_1479)::[])
in (_140_1481)::_140_1480))))))
in (

let mk_ref = (fun reft_name _50_2147 -> (

let r = ("r", FStar_ToSMT_Term.Ref_sort)
in (

let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (

let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (

let refa = (let _140_1488 = (let _140_1487 = (let _140_1486 = (FStar_ToSMT_Term.mkFreeV aa)
in (_140_1486)::[])
in (reft_name, _140_1487))
in (FStar_ToSMT_Term.mkApp _140_1488))
in (

let refb = (let _140_1491 = (let _140_1490 = (let _140_1489 = (FStar_ToSMT_Term.mkFreeV bb)
in (_140_1489)::[])
in (reft_name, _140_1490))
in (FStar_ToSMT_Term.mkApp _140_1491))
in (

let typing_pred = (FStar_ToSMT_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_ToSMT_Term.mk_HasType x refb)
in (let _140_1510 = (let _140_1497 = (let _140_1496 = (let _140_1495 = (let _140_1494 = (let _140_1493 = (let _140_1492 = (FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _140_1492))
in (FStar_ToSMT_Term.mkImp _140_1493))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _140_1494))
in (mkForall_fuel _140_1495))
in (_140_1496, Some ("ref inversion")))
in FStar_ToSMT_Term.Assume (_140_1497))
in (let _140_1509 = (let _140_1508 = (let _140_1507 = (let _140_1506 = (let _140_1505 = (let _140_1504 = (let _140_1503 = (let _140_1502 = (FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _140_1501 = (let _140_1500 = (let _140_1499 = (FStar_ToSMT_Term.mkFreeV aa)
in (let _140_1498 = (FStar_ToSMT_Term.mkFreeV bb)
in (_140_1499, _140_1498)))
in (FStar_ToSMT_Term.mkEq _140_1500))
in (_140_1502, _140_1501)))
in (FStar_ToSMT_Term.mkImp _140_1503))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _140_1504))
in (mkForall_fuel' 2 _140_1505))
in (_140_1506, Some ("ref typing is injective")))
in FStar_ToSMT_Term.Assume (_140_1507))
in (_140_1508)::[])
in (_140_1510)::_140_1509))))))))))
in (

let mk_false_interp = (fun _50_2157 false_tm -> (

let valid = (FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _140_1517 = (let _140_1516 = (let _140_1515 = (FStar_ToSMT_Term.mkIff (FStar_ToSMT_Term.mkFalse, valid))
in (_140_1515, Some ("False interpretation")))
in FStar_ToSMT_Term.Assume (_140_1516))
in (_140_1517)::[])))
in (

let mk_and_interp = (fun conj _50_2163 -> (

let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (

let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _140_1524 = (let _140_1523 = (let _140_1522 = (FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_140_1522)::[])
in ("Valid", _140_1523))
in (FStar_ToSMT_Term.mkApp _140_1524))
in (

let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _140_1531 = (let _140_1530 = (let _140_1529 = (let _140_1528 = (let _140_1527 = (let _140_1526 = (let _140_1525 = (FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_140_1525, valid))
in (FStar_ToSMT_Term.mkIff _140_1526))
in (((valid)::[])::[], (aa)::(bb)::[], _140_1527))
in (FStar_ToSMT_Term.mkForall _140_1528))
in (_140_1529, Some ("/\\ interpretation")))
in FStar_ToSMT_Term.Assume (_140_1530))
in (_140_1531)::[])))))))))
in (

let mk_or_interp = (fun disj _50_2174 -> (

let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (

let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _140_1538 = (let _140_1537 = (let _140_1536 = (FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_140_1536)::[])
in ("Valid", _140_1537))
in (FStar_ToSMT_Term.mkApp _140_1538))
in (

let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _140_1545 = (let _140_1544 = (let _140_1543 = (let _140_1542 = (let _140_1541 = (let _140_1540 = (let _140_1539 = (FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_140_1539, valid))
in (FStar_ToSMT_Term.mkIff _140_1540))
in (((valid)::[])::[], (aa)::(bb)::[], _140_1541))
in (FStar_ToSMT_Term.mkForall _140_1542))
in (_140_1543, Some ("\\/ interpretation")))
in FStar_ToSMT_Term.Assume (_140_1544))
in (_140_1545)::[])))))))))
in (

let mk_eq2_interp = (fun eq2 tt -> (

let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (

let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (

let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (

let yy = ("y", FStar_ToSMT_Term.Term_sort)
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let y = (FStar_ToSMT_Term.mkFreeV yy)
in (

let valid = (let _140_1552 = (let _140_1551 = (let _140_1550 = (FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_140_1550)::[])
in ("Valid", _140_1551))
in (FStar_ToSMT_Term.mkApp _140_1552))
in (let _140_1559 = (let _140_1558 = (let _140_1557 = (let _140_1556 = (let _140_1555 = (let _140_1554 = (let _140_1553 = (FStar_ToSMT_Term.mkEq (x, y))
in (_140_1553, valid))
in (FStar_ToSMT_Term.mkIff _140_1554))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _140_1555))
in (FStar_ToSMT_Term.mkForall _140_1556))
in (_140_1557, Some ("Eq2 interpretation")))
in FStar_ToSMT_Term.Assume (_140_1558))
in (_140_1559)::[])))))))))))
in (

let mk_imp_interp = (fun imp tt -> (

let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (

let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _140_1566 = (let _140_1565 = (let _140_1564 = (FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_140_1564)::[])
in ("Valid", _140_1565))
in (FStar_ToSMT_Term.mkApp _140_1566))
in (

let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _140_1573 = (let _140_1572 = (let _140_1571 = (let _140_1570 = (let _140_1569 = (let _140_1568 = (let _140_1567 = (FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_140_1567, valid))
in (FStar_ToSMT_Term.mkIff _140_1568))
in (((valid)::[])::[], (aa)::(bb)::[], _140_1569))
in (FStar_ToSMT_Term.mkForall _140_1570))
in (_140_1571, Some ("==> interpretation")))
in FStar_ToSMT_Term.Assume (_140_1572))
in (_140_1573)::[])))))))))
in (

let mk_iff_interp = (fun iff tt -> (

let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (

let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _140_1580 = (let _140_1579 = (let _140_1578 = (FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_140_1578)::[])
in ("Valid", _140_1579))
in (FStar_ToSMT_Term.mkApp _140_1580))
in (

let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (

let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _140_1587 = (let _140_1586 = (let _140_1585 = (let _140_1584 = (let _140_1583 = (let _140_1582 = (let _140_1581 = (FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_140_1581, valid))
in (FStar_ToSMT_Term.mkIff _140_1582))
in (((valid)::[])::[], (aa)::(bb)::[], _140_1583))
in (FStar_ToSMT_Term.mkForall _140_1584))
in (_140_1585, Some ("<==> interpretation")))
in FStar_ToSMT_Term.Assume (_140_1586))
in (_140_1587)::[])))))))))
in (

let mk_forall_interp = (fun for_all tt -> (

let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (

let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (

let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let valid = (let _140_1594 = (let _140_1593 = (let _140_1592 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_140_1592)::[])
in ("Valid", _140_1593))
in (FStar_ToSMT_Term.mkApp _140_1594))
in (

let valid_b_x = (let _140_1597 = (let _140_1596 = (let _140_1595 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_140_1595)::[])
in ("Valid", _140_1596))
in (FStar_ToSMT_Term.mkApp _140_1597))
in (let _140_1611 = (let _140_1610 = (let _140_1609 = (let _140_1608 = (let _140_1607 = (let _140_1606 = (let _140_1605 = (let _140_1604 = (let _140_1603 = (let _140_1599 = (let _140_1598 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_140_1598)::[])
in (_140_1599)::[])
in (let _140_1602 = (let _140_1601 = (let _140_1600 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_140_1600, valid_b_x))
in (FStar_ToSMT_Term.mkImp _140_1601))
in (_140_1603, (xx)::[], _140_1602)))
in (FStar_ToSMT_Term.mkForall _140_1604))
in (_140_1605, valid))
in (FStar_ToSMT_Term.mkIff _140_1606))
in (((valid)::[])::[], (aa)::(bb)::[], _140_1607))
in (FStar_ToSMT_Term.mkForall _140_1608))
in (_140_1609, Some ("forall interpretation")))
in FStar_ToSMT_Term.Assume (_140_1610))
in (_140_1611)::[]))))))))))
in (

let mk_exists_interp = (fun for_all tt -> (

let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (

let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (

let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let valid = (let _140_1618 = (let _140_1617 = (let _140_1616 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_140_1616)::[])
in ("Valid", _140_1617))
in (FStar_ToSMT_Term.mkApp _140_1618))
in (

let valid_b_x = (let _140_1621 = (let _140_1620 = (let _140_1619 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_140_1619)::[])
in ("Valid", _140_1620))
in (FStar_ToSMT_Term.mkApp _140_1621))
in (let _140_1635 = (let _140_1634 = (let _140_1633 = (let _140_1632 = (let _140_1631 = (let _140_1630 = (let _140_1629 = (let _140_1628 = (let _140_1627 = (let _140_1623 = (let _140_1622 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_140_1622)::[])
in (_140_1623)::[])
in (let _140_1626 = (let _140_1625 = (let _140_1624 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_140_1624, valid_b_x))
in (FStar_ToSMT_Term.mkImp _140_1625))
in (_140_1627, (xx)::[], _140_1626)))
in (FStar_ToSMT_Term.mkExists _140_1628))
in (_140_1629, valid))
in (FStar_ToSMT_Term.mkIff _140_1630))
in (((valid)::[])::[], (aa)::(bb)::[], _140_1631))
in (FStar_ToSMT_Term.mkForall _140_1632))
in (_140_1633, Some ("exists interpretation")))
in FStar_ToSMT_Term.Assume (_140_1634))
in (_140_1635)::[]))))))))))
in (

let mk_foralltyp_interp = (fun for_all tt -> (

let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (

let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (

let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (

let k = (FStar_ToSMT_Term.mkFreeV kk)
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _140_1642 = (let _140_1641 = (let _140_1640 = (FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_140_1640)::[])
in ("Valid", _140_1641))
in (FStar_ToSMT_Term.mkApp _140_1642))
in (

let valid_a_b = (let _140_1645 = (let _140_1644 = (let _140_1643 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_140_1643)::[])
in ("Valid", _140_1644))
in (FStar_ToSMT_Term.mkApp _140_1645))
in (let _140_1659 = (let _140_1658 = (let _140_1657 = (let _140_1656 = (let _140_1655 = (let _140_1654 = (let _140_1653 = (let _140_1652 = (let _140_1651 = (let _140_1647 = (let _140_1646 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_140_1646)::[])
in (_140_1647)::[])
in (let _140_1650 = (let _140_1649 = (let _140_1648 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_140_1648, valid_a_b))
in (FStar_ToSMT_Term.mkImp _140_1649))
in (_140_1651, (bb)::[], _140_1650)))
in (FStar_ToSMT_Term.mkForall _140_1652))
in (_140_1653, valid))
in (FStar_ToSMT_Term.mkIff _140_1654))
in (((valid)::[])::[], (kk)::(aa)::[], _140_1655))
in (FStar_ToSMT_Term.mkForall _140_1656))
in (_140_1657, Some ("ForallTyp interpretation")))
in FStar_ToSMT_Term.Assume (_140_1658))
in (_140_1659)::[]))))))))))
in (

let mk_existstyp_interp = (fun for_some tt -> (

let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (

let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (

let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (

let k = (FStar_ToSMT_Term.mkFreeV kk)
in (

let a = (FStar_ToSMT_Term.mkFreeV aa)
in (

let b = (FStar_ToSMT_Term.mkFreeV bb)
in (

let valid = (let _140_1666 = (let _140_1665 = (let _140_1664 = (FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_140_1664)::[])
in ("Valid", _140_1665))
in (FStar_ToSMT_Term.mkApp _140_1666))
in (

let valid_a_b = (let _140_1669 = (let _140_1668 = (let _140_1667 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_140_1667)::[])
in ("Valid", _140_1668))
in (FStar_ToSMT_Term.mkApp _140_1669))
in (let _140_1683 = (let _140_1682 = (let _140_1681 = (let _140_1680 = (let _140_1679 = (let _140_1678 = (let _140_1677 = (let _140_1676 = (let _140_1675 = (let _140_1671 = (let _140_1670 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_140_1670)::[])
in (_140_1671)::[])
in (let _140_1674 = (let _140_1673 = (let _140_1672 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_140_1672, valid_a_b))
in (FStar_ToSMT_Term.mkImp _140_1673))
in (_140_1675, (bb)::[], _140_1674)))
in (FStar_ToSMT_Term.mkExists _140_1676))
in (_140_1677, valid))
in (FStar_ToSMT_Term.mkIff _140_1678))
in (((valid)::[])::[], (kk)::(aa)::[], _140_1679))
in (FStar_ToSMT_Term.mkForall _140_1680))
in (_140_1681, Some ("ExistsTyp interpretation")))
in FStar_ToSMT_Term.Assume (_140_1682))
in (_140_1683)::[]))))))))))
in (

let prims = ((FStar_Absyn_Const.unit_lid, mk_unit))::((FStar_Absyn_Const.bool_lid, mk_bool))::((FStar_Absyn_Const.int_lid, mk_int))::((FStar_Absyn_Const.string_lid, mk_str))::((FStar_Absyn_Const.ref_lid, mk_ref))::((FStar_Absyn_Const.false_lid, mk_false_interp))::((FStar_Absyn_Const.and_lid, mk_and_interp))::((FStar_Absyn_Const.or_lid, mk_or_interp))::((FStar_Absyn_Const.eq2_lid, mk_eq2_interp))::((FStar_Absyn_Const.imp_lid, mk_imp_interp))::((FStar_Absyn_Const.iff_lid, mk_iff_interp))::((FStar_Absyn_Const.forall_lid, mk_forall_interp))::((FStar_Absyn_Const.exists_lid, mk_exists_interp))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _50_2267 -> (match (_50_2267) with
| (l, _50_2266) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_50_2270, f) -> begin
(f s tt)
end)))))))))))))))))))))))


let rec encode_sigelt : env_t  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_ToSMT_Term.decls_t * env_t) = (fun env se -> (

let _50_2276 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _140_1814 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _140_1814))
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

let _50_2284 = (encode_sigelt' env se)
in (match (_50_2284) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _140_1817 = (let _140_1816 = (let _140_1815 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_ToSMT_Term.Caption (_140_1815))
in (_140_1816)::[])
in (_140_1817, e))
end
| _50_2287 -> begin
(let _140_1824 = (let _140_1823 = (let _140_1819 = (let _140_1818 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_140_1818))
in (_140_1819)::g)
in (let _140_1822 = (let _140_1821 = (let _140_1820 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_140_1820))
in (_140_1821)::[])
in (FStar_List.append _140_1823 _140_1822)))
in (_140_1824, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_ToSMT_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> ((((FStar_Util.starts_with l.FStar_Ident.str "Prims.pure_") || (FStar_Util.starts_with l.FStar_Ident.str "Prims.ex_")) || (FStar_Util.starts_with l.FStar_Ident.str "Prims.st_")) || (FStar_Util.starts_with l.FStar_Ident.str "Prims.all_")))
in (

let encode_top_level_val = (fun env lid t quals -> (

let tt = (whnf env t)
in (

let _50_2300 = (encode_free_var env lid t tt quals)
in (match (_50_2300) with
| (decls, env) -> begin
if (FStar_Absyn_Util.is_smt_lemma t) then begin
(let _140_1838 = (let _140_1837 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _140_1837))
in (_140_1838, env))
end else begin
(decls, env)
end
end))))
in (

let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _50_2307 lb -> (match (_50_2307) with
| (decls, env) -> begin
(

let _50_2311 = (let _140_1847 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (encode_top_level_val env _140_1847 lb.FStar_Absyn_Syntax.lbtyp quals))
in (match (_50_2311) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_50_2313, _50_2315, _50_2317, _50_2319, (FStar_Absyn_Syntax.Effect)::[], _50_2323) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _50_2328, _50_2330, _50_2332, _50_2334, _50_2336) when (should_skip lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _50_2341, _50_2343, _50_2345, _50_2347, _50_2349) when (FStar_Ident.lid_equals lid FStar_Absyn_Const.b2t_lid) -> begin
(

let _50_2355 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_50_2355) with
| (tname, ttok, env) -> begin
(

let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (

let x = (FStar_ToSMT_Term.mkFreeV xx)
in (

let valid_b2t_x = (let _140_1850 = (let _140_1849 = (let _140_1848 = (FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (_140_1848)::[])
in ("Valid", _140_1849))
in (FStar_ToSMT_Term.mkApp _140_1850))
in (

let decls = (let _140_1858 = (let _140_1857 = (let _140_1856 = (let _140_1855 = (let _140_1854 = (let _140_1853 = (let _140_1852 = (let _140_1851 = (FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _140_1851))
in (FStar_ToSMT_Term.mkEq _140_1852))
in (((valid_b2t_x)::[])::[], (xx)::[], _140_1853))
in (FStar_ToSMT_Term.mkForall _140_1854))
in (_140_1855, Some ("b2t def")))
in FStar_ToSMT_Term.Assume (_140_1856))
in (_140_1857)::[])
in (FStar_ToSMT_Term.DeclFun ((tname, (FStar_ToSMT_Term.Term_sort)::[], FStar_ToSMT_Term.Type_sort, None)))::_140_1858)
in (decls, env)))))
end))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _50_2363, t, tags, _50_2367) -> begin
(

let _50_2373 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_50_2373) with
| (tname, ttok, env) -> begin
(

let _50_2382 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (tps', body) -> begin
((FStar_List.append tps tps'), body)
end
| _50_2379 -> begin
(tps, t)
end)
in (match (_50_2382) with
| (tps, t) -> begin
(

let _50_2389 = (encode_binders None tps env)
in (match (_50_2389) with
| (vars, guards, env', binder_decls, _50_2388) -> begin
(

let tok_app = (let _140_1859 = (FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _140_1859 vars))
in (

let tok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, None))
in (

let app = (let _140_1861 = (let _140_1860 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _140_1860))
in (FStar_ToSMT_Term.mkApp _140_1861))
in (

let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _50_2395 -> begin
(let _140_1863 = (let _140_1862 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _140_1862))
in (_140_1863)::[])
end)
in (

let decls = (let _140_1874 = (let _140_1867 = (let _140_1866 = (let _140_1865 = (let _140_1864 = (FStar_List.map Prims.snd vars)
in (tname, _140_1864, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_140_1865))
in (_140_1866)::(tok_decl)::[])
in (FStar_List.append _140_1867 fresh_tok))
in (let _140_1873 = (let _140_1872 = (let _140_1871 = (let _140_1870 = (let _140_1869 = (let _140_1868 = (FStar_ToSMT_Term.mkEq (tok_app, app))
in (((tok_app)::[])::[], vars, _140_1868))
in (FStar_ToSMT_Term.mkForall _140_1869))
in (_140_1870, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_140_1871))
in (_140_1872)::[])
in (FStar_List.append _140_1874 _140_1873)))
in (

let t = if (FStar_All.pipe_right tags (FStar_List.contains FStar_Absyn_Syntax.Opaque)) then begin
(FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
end else begin
(whnf env t)
end
in (

let _50_2407 = if (FStar_All.pipe_right tags (FStar_Util.for_some (fun _50_18 -> (match (_50_18) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _50_2402 -> begin
false
end)))) then begin
(let _140_1877 = (FStar_ToSMT_Term.mk_Valid app)
in (let _140_1876 = (encode_formula t env')
in (_140_1877, _140_1876)))
end else begin
(let _140_1878 = (encode_typ_term t env')
in (app, _140_1878))
end
in (match (_50_2407) with
| (def, (body, decls1)) -> begin
(

let abbrev_def = (let _140_1885 = (let _140_1884 = (let _140_1883 = (let _140_1882 = (let _140_1881 = (let _140_1880 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _140_1879 = (FStar_ToSMT_Term.mkEq (def, body))
in (_140_1880, _140_1879)))
in (FStar_ToSMT_Term.mkImp _140_1881))
in (((def)::[])::[], vars, _140_1882))
in (FStar_ToSMT_Term.mkForall _140_1883))
in (_140_1884, Some ("abbrev. elimination")))
in FStar_ToSMT_Term.Assume (_140_1885))
in (

let kindingAx = (

let _50_2411 = (let _140_1886 = (FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _140_1886 env' app))
in (match (_50_2411) with
| (k, decls) -> begin
(let _140_1894 = (let _140_1893 = (let _140_1892 = (let _140_1891 = (let _140_1890 = (let _140_1889 = (let _140_1888 = (let _140_1887 = (FStar_ToSMT_Term.mk_and_l guards)
in (_140_1887, k))
in (FStar_ToSMT_Term.mkImp _140_1888))
in (((app)::[])::[], vars, _140_1889))
in (FStar_ToSMT_Term.mkForall _140_1890))
in (_140_1891, Some ("abbrev. kinding")))
in FStar_ToSMT_Term.Assume (_140_1892))
in (_140_1893)::[])
in (FStar_List.append decls _140_1894))
end))
in (

let g = (let _140_1895 = (primitive_type_axioms lid tname app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _140_1895))
in (g, env))))
end))))))))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _50_2418) -> begin
if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || env.tcenv.FStar_Tc_Env.is_iface) then begin
(encode_top_level_val env lid t quals)
end else begin
([], env)
end
end
| FStar_Absyn_Syntax.Sig_assume (l, f, _50_2424, _50_2426) -> begin
(

let _50_2431 = (encode_formula f env)
in (match (_50_2431) with
| (f, decls) -> begin
(

let g = (let _140_1900 = (let _140_1899 = (let _140_1898 = (let _140_1897 = (let _140_1896 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "Assumption: %s" _140_1896))
in Some (_140_1897))
in (f, _140_1898))
in FStar_ToSMT_Term.Assume (_140_1899))
in (_140_1900)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _50_2437, datas, quals, _50_2441) when (FStar_Ident.lid_equals t FStar_Absyn_Const.precedes_lid) -> begin
(

let _50_2447 = (new_typ_constant_and_tok_from_lid env t)
in (match (_50_2447) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, _50_2450, _50_2452, _50_2454, _50_2456, _50_2458, _50_2460) when ((FStar_Ident.lid_equals t FStar_Absyn_Const.char_lid) || (FStar_Ident.lid_equals t FStar_Absyn_Const.uint8_lid)) -> begin
(

let tname = t.FStar_Ident.str
in (

let tsym = (FStar_ToSMT_Term.mkFreeV (tname, FStar_ToSMT_Term.Type_sort))
in (

let decl = FStar_ToSMT_Term.DeclFun ((tname, [], FStar_ToSMT_Term.Type_sort, None))
in (let _140_1902 = (let _140_1901 = (primitive_type_axioms t tname tsym)
in (decl)::_140_1901)
in (_140_1902, (push_free_tvar env t tname (Some (tsym))))))))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _50_2470, datas, quals, _50_2474) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _50_19 -> (match (_50_19) with
| (FStar_Absyn_Syntax.Logic) | (FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _50_2481 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _50_2491 = c
in (match (_50_2491) with
| (name, args, _50_2488, _50_2490) -> begin
(let _140_1908 = (let _140_1907 = (let _140_1906 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _140_1906, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_140_1907))
in (_140_1908)::[])
end))
end else begin
(FStar_ToSMT_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (((FStar_List.length datas) = 0) || (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _140_1914 = (FStar_Tc_Env.lookup_qname env.tcenv l)
in (FStar_All.pipe_right _140_1914 FStar_Option.isNone)))))) then begin
[]
end else begin
(

let _50_2498 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_50_2498) with
| (xxsym, xx) -> begin
(

let _50_2541 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _50_2501 l -> (match (_50_2501) with
| (out, decls) -> begin
(

let data_t = (FStar_Tc_Env.lookup_datacon env.tcenv l)
in (

let _50_2511 = (match ((FStar_Absyn_Util.function_formals data_t)) with
| Some (formals, res) -> begin
(formals, (FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_50_2511) with
| (args, res) -> begin
(

let indices = (match ((let _140_1917 = (FStar_Absyn_Util.compress_typ res)
in _140_1917.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (_50_2513, indices) -> begin
indices
end
| _50_2518 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (a) -> begin
(let _140_1922 = (let _140_1921 = (let _140_1920 = (mk_typ_projector_name l a.FStar_Absyn_Syntax.v)
in (_140_1920, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _140_1921))
in (push_typ_var env a.FStar_Absyn_Syntax.v _140_1922))
end
| FStar_Util.Inr (x) -> begin
(let _140_1925 = (let _140_1924 = (let _140_1923 = (mk_term_projector_name l x.FStar_Absyn_Syntax.v)
in (_140_1923, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _140_1924))
in (push_term_var env x.FStar_Absyn_Syntax.v _140_1925))
end)) env))
in (

let _50_2529 = (encode_args indices env)
in (match (_50_2529) with
| (indices, decls') -> begin
(

let _50_2530 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _140_1932 = (FStar_List.map2 (fun v a -> (match (a) with
| FStar_Util.Inl (a) -> begin
(let _140_1929 = (let _140_1928 = (FStar_ToSMT_Term.mkFreeV v)
in (_140_1928, a))
in (FStar_ToSMT_Term.mkEq _140_1929))
end
| FStar_Util.Inr (a) -> begin
(let _140_1931 = (let _140_1930 = (FStar_ToSMT_Term.mkFreeV v)
in (_140_1930, a))
in (FStar_ToSMT_Term.mkEq _140_1931))
end)) vars indices)
in (FStar_All.pipe_right _140_1932 FStar_ToSMT_Term.mk_and_l))
in (let _140_1937 = (let _140_1936 = (let _140_1935 = (let _140_1934 = (let _140_1933 = (mk_data_tester env l xx)
in (_140_1933, eqs))
in (FStar_ToSMT_Term.mkAnd _140_1934))
in (out, _140_1935))
in (FStar_ToSMT_Term.mkOr _140_1936))
in (_140_1937, (FStar_List.append decls decls')))))
end))))
end)))
end)) (FStar_ToSMT_Term.mkFalse, [])))
in (match (_50_2541) with
| (data_ax, decls) -> begin
(

let _50_2544 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_50_2544) with
| (ffsym, ff) -> begin
(

let xx_has_type = (let _140_1938 = (FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_ToSMT_Term.mk_HasTypeFuel _140_1938 xx tapp))
in (let _140_1945 = (let _140_1944 = (let _140_1943 = (let _140_1942 = (let _140_1941 = (let _140_1940 = (add_fuel (ffsym, FStar_ToSMT_Term.Fuel_sort) (((xxsym, FStar_ToSMT_Term.Term_sort))::vars))
in (let _140_1939 = (FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _140_1940, _140_1939)))
in (FStar_ToSMT_Term.mkForall _140_1941))
in (_140_1942, Some ("inversion axiom")))
in FStar_ToSMT_Term.Assume (_140_1943))
in (_140_1944)::[])
in (FStar_List.append decls _140_1945)))
end))
end))
end))
end)
in (

let k = (FStar_Absyn_Util.close_kind tps k)
in (

let _50_2556 = (match ((let _140_1946 = (FStar_Absyn_Util.compress_kind k)
in _140_1946.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_arrow (bs, res) -> begin
(true, bs, res)
end
| _50_2552 -> begin
(false, [], k)
end)
in (match (_50_2556) with
| (is_kind_arrow, formals, res) -> begin
(

let _50_2563 = (encode_binders None formals env)
in (match (_50_2563) with
| (vars, guards, env', binder_decls, _50_2562) -> begin
(

let projection_axioms = (fun tapp vars -> (match ((FStar_All.pipe_right quals (FStar_Util.find_opt (fun _50_20 -> (match (_50_20) with
| FStar_Absyn_Syntax.Projector (_50_2569) -> begin
true
end
| _50_2572 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.Projector (d, FStar_Util.Inl (a))) -> begin
(

let rec projectee = (fun i _50_21 -> (match (_50_21) with
| [] -> begin
i
end
| (f)::tl -> begin
(match ((Prims.fst f)) with
| FStar_Util.Inl (_50_2587) -> begin
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
in (

let projectee_pos = (projectee 0 formals)
in (

let _50_2602 = (match ((FStar_Util.first_N projectee_pos vars)) with
| (_50_2593, (xx)::suffix) -> begin
(xx, suffix)
end
| _50_2599 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_50_2602) with
| (xx, suffix) -> begin
(

let dproj_app = (let _140_1960 = (let _140_1959 = (let _140_1958 = (mk_typ_projector_name d a)
in (let _140_1957 = (let _140_1956 = (FStar_ToSMT_Term.mkFreeV xx)
in (_140_1956)::[])
in (_140_1958, _140_1957)))
in (FStar_ToSMT_Term.mkApp _140_1959))
in (mk_ApplyT _140_1960 suffix))
in (let _140_1965 = (let _140_1964 = (let _140_1963 = (let _140_1962 = (let _140_1961 = (FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in (((tapp)::[])::[], vars, _140_1961))
in (FStar_ToSMT_Term.mkForall _140_1962))
in (_140_1963, Some ("projector axiom")))
in FStar_ToSMT_Term.Assume (_140_1964))
in (_140_1965)::[]))
end))))
end
| _50_2605 -> begin
[]
end))
in (

let pretype_axioms = (fun tapp vars -> (

let _50_2611 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_50_2611) with
| (xxsym, xx) -> begin
(

let _50_2614 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_50_2614) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _140_1978 = (let _140_1977 = (let _140_1976 = (let _140_1975 = (let _140_1974 = (let _140_1973 = (let _140_1972 = (let _140_1971 = (let _140_1970 = (FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _140_1970))
in (FStar_ToSMT_Term.mkEq _140_1971))
in (xx_has_type, _140_1972))
in (FStar_ToSMT_Term.mkImp _140_1973))
in (((xx_has_type)::[])::[], ((xxsym, FStar_ToSMT_Term.Term_sort))::((ffsym, FStar_ToSMT_Term.Fuel_sort))::vars, _140_1974))
in (FStar_ToSMT_Term.mkForall _140_1975))
in (_140_1976, Some ("pretyping")))
in FStar_ToSMT_Term.Assume (_140_1977))
in (_140_1978)::[]))
end))
end)))
in (

let _50_2619 = (new_typ_constant_and_tok_from_lid env t)
in (match (_50_2619) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_ToSMT_Term.mkApp (ttok, []))
in (

let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (

let tapp = (let _140_1980 = (let _140_1979 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _140_1979))
in (FStar_ToSMT_Term.mkApp _140_1980))
in (

let _50_2640 = (

let tname_decl = (let _140_1984 = (let _140_1983 = (FStar_All.pipe_right vars (FStar_List.map (fun _50_2625 -> (match (_50_2625) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _140_1982 = (varops.next_id ())
in (tname, _140_1983, FStar_ToSMT_Term.Type_sort, _140_1982)))
in (constructor_or_logic_type_decl _140_1984))
in (

let _50_2637 = (match (vars) with
| [] -> begin
(let _140_1988 = (let _140_1987 = (let _140_1986 = (FStar_ToSMT_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _140_1985 -> Some (_140_1985)) _140_1986))
in (push_free_tvar env t tname _140_1987))
in ([], _140_1988))
end
| _50_2629 -> begin
(

let ttok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, Some ("token")))
in (

let ttok_fresh = (let _140_1989 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _140_1989))
in (

let ttok_app = (mk_ApplyT ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _140_1993 = (let _140_1992 = (let _140_1991 = (let _140_1990 = (FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _140_1990))
in (FStar_ToSMT_Term.mkForall' _140_1991))
in (_140_1992, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_140_1993))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_50_2637) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_50_2640) with
| (decls, env) -> begin
(

let kindingAx = (

let _50_2643 = (encode_knd res env' tapp)
in (match (_50_2643) with
| (k, decls) -> begin
(

let karr = if is_kind_arrow then begin
(let _140_1997 = (let _140_1996 = (let _140_1995 = (let _140_1994 = (FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _140_1994))
in (_140_1995, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_140_1996))
in (_140_1997)::[])
end else begin
[]
end
in (let _140_2003 = (let _140_2002 = (let _140_2001 = (let _140_2000 = (let _140_1999 = (let _140_1998 = (FStar_ToSMT_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _140_1998))
in (FStar_ToSMT_Term.mkForall _140_1999))
in (_140_2000, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_140_2001))
in (_140_2002)::[])
in (FStar_List.append (FStar_List.append decls karr) _140_2003)))
end))
in (

let aux = if is_logical then begin
(let _140_2004 = (projection_axioms tapp vars)
in (FStar_List.append kindingAx _140_2004))
end else begin
(let _140_2011 = (let _140_2009 = (let _140_2007 = (let _140_2005 = (primitive_type_axioms t tname tapp)
in (FStar_List.append kindingAx _140_2005))
in (let _140_2006 = (inversion_axioms tapp vars)
in (FStar_List.append _140_2007 _140_2006)))
in (let _140_2008 = (projection_axioms tapp vars)
in (FStar_List.append _140_2009 _140_2008)))
in (let _140_2010 = (pretype_axioms tapp vars)
in (FStar_List.append _140_2011 _140_2010)))
end
in (

let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))))
end))
end))))))
end
| FStar_Absyn_Syntax.Sig_datacon (d, _50_2650, _50_2652, _50_2654, _50_2656, _50_2658) when (FStar_Ident.lid_equals d FStar_Absyn_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_datacon (d, t, (_50_2664, tps, _50_2667), quals, _50_2671, drange) -> begin
(

let t = (let _140_2013 = (FStar_List.map (fun _50_2678 -> (match (_50_2678) with
| (x, _50_2677) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit (true)))
end)) tps)
in (FStar_Absyn_Util.close_typ _140_2013 t))
in (

let _50_2683 = (new_term_constant_and_tok_from_lid env d)
in (match (_50_2683) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_ToSMT_Term.mkApp (ddtok, []))
in (

let _50_2692 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
(f, (FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_50_2692) with
| (formals, t_res) -> begin
(

let _50_2695 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_50_2695) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (

let _50_2702 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_50_2702) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun _50_22 -> (match (_50_22) with
| FStar_Util.Inl (a) -> begin
(let _140_2015 = (mk_typ_projector_name d a)
in (_140_2015, FStar_ToSMT_Term.Type_sort))
end
| FStar_Util.Inr (x) -> begin
(let _140_2016 = (mk_term_projector_name d x)
in (_140_2016, FStar_ToSMT_Term.Term_sort))
end))))
in (

let datacons = (let _140_2018 = (let _140_2017 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_ToSMT_Term.Term_sort, _140_2017))
in (FStar_All.pipe_right _140_2018 FStar_ToSMT_Term.constructor_to_decl))
in (

let app = (mk_ApplyE ddtok_tm vars)
in (

let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (

let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (

let _50_2716 = (encode_typ_pred None t env ddtok_tm)
in (match (_50_2716) with
| (tok_typing, decls3) -> begin
(

let _50_2723 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_50_2723) with
| (vars', guards', env'', decls_formals, _50_2722) -> begin
(

let _50_2728 = (

let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars')
in (

let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_50_2728) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_ToSMT_Term.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _50_2732 -> begin
(let _140_2020 = (let _140_2019 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ddtok, FStar_ToSMT_Term.Term_sort) _140_2019))
in (_140_2020)::[])
end)
in (

let encode_elim = (fun _50_2735 -> (match (()) with
| () -> begin
(

let _50_2738 = (FStar_Absyn_Util.head_and_args t_res)
in (match (_50_2738) with
| (head, args) -> begin
(match ((let _140_2023 = (FStar_Absyn_Util.compress_typ head)
in _140_2023.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(

let encoded_head = (lookup_free_tvar_name env' fv)
in (

let _50_2744 = (encode_args args env')
in (match (_50_2744) with
| (encoded_args, arg_decls) -> begin
(

let _50_2768 = (FStar_List.fold_left (fun _50_2748 arg -> (match (_50_2748) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| FStar_Util.Inl (targ) -> begin
(

let _50_2756 = (let _140_2026 = (FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _140_2026))
in (match (_50_2756) with
| (_50_2753, tv, env) -> begin
(let _140_2028 = (let _140_2027 = (FStar_ToSMT_Term.mkEq (targ, tv))
in (_140_2027)::eqns)
in (env, (tv)::arg_vars, _140_2028))
end))
end
| FStar_Util.Inr (varg) -> begin
(

let _50_2763 = (let _140_2029 = (FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _140_2029))
in (match (_50_2763) with
| (_50_2760, xv, env) -> begin
(let _140_2031 = (let _140_2030 = (FStar_ToSMT_Term.mkEq (varg, xv))
in (_140_2030)::eqns)
in (env, (xv)::arg_vars, _140_2031))
end))
end)
end)) (env', [], []) encoded_args)
in (match (_50_2768) with
| (_50_2765, arg_vars, eqns) -> begin
(

let arg_vars = (FStar_List.rev arg_vars)
in (

let ty = (FStar_ToSMT_Term.mkApp (encoded_head, arg_vars))
in (

let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (

let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (

let ty_pred = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (

let arg_binders = (FStar_List.map FStar_ToSMT_Term.fv_of_term arg_vars)
in (

let typing_inversion = (let _140_2038 = (let _140_2037 = (let _140_2036 = (let _140_2035 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _140_2034 = (let _140_2033 = (let _140_2032 = (FStar_ToSMT_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _140_2032))
in (FStar_ToSMT_Term.mkImp _140_2033))
in (((ty_pred)::[])::[], _140_2035, _140_2034)))
in (FStar_ToSMT_Term.mkForall _140_2036))
in (_140_2037, Some ("data constructor typing elim")))
in FStar_ToSMT_Term.Assume (_140_2038))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Absyn_Const.lextop_lid) then begin
(

let x = (let _140_2039 = (varops.fresh "x")
in (_140_2039, FStar_ToSMT_Term.Term_sort))
in (

let xtm = (FStar_ToSMT_Term.mkFreeV x)
in (let _140_2049 = (let _140_2048 = (let _140_2047 = (let _140_2046 = (let _140_2041 = (let _140_2040 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_140_2040)::[])
in (_140_2041)::[])
in (let _140_2045 = (let _140_2044 = (let _140_2043 = (FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _140_2042 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_140_2043, _140_2042)))
in (FStar_ToSMT_Term.mkImp _140_2044))
in (_140_2046, (x)::[], _140_2045)))
in (FStar_ToSMT_Term.mkForall _140_2047))
in (_140_2048, Some ("lextop is top")))
in FStar_ToSMT_Term.Assume (_140_2049))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| (FStar_ToSMT_Term.Type_sort) | (FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| FStar_ToSMT_Term.Term_sort -> begin
(let _140_2052 = (let _140_2051 = (FStar_ToSMT_Term.mkFreeV v)
in (FStar_ToSMT_Term.mk_Precedes _140_2051 dapp))
in (_140_2052)::[])
end
| _50_2783 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _140_2059 = (let _140_2058 = (let _140_2057 = (let _140_2056 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _140_2055 = (let _140_2054 = (let _140_2053 = (FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _140_2053))
in (FStar_ToSMT_Term.mkImp _140_2054))
in (((ty_pred)::[])::[], _140_2056, _140_2055)))
in (FStar_ToSMT_Term.mkForall _140_2057))
in (_140_2058, Some ("subterm ordering")))
in FStar_ToSMT_Term.Assume (_140_2059)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _50_2787 -> begin
(

let _50_2788 = (let _140_2062 = (let _140_2061 = (FStar_Absyn_Print.sli d)
in (let _140_2060 = (FStar_Absyn_Print.typ_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _140_2061 _140_2060)))
in (FStar_Tc_Errors.warn drange _140_2062))
in ([], []))
end)
end))
end))
in (

let _50_2792 = (encode_elim ())
in (match (_50_2792) with
| (decls2, elim) -> begin
(

let g = (let _140_2087 = (let _140_2086 = (let _140_2071 = (let _140_2070 = (let _140_2069 = (let _140_2068 = (let _140_2067 = (let _140_2066 = (let _140_2065 = (let _140_2064 = (let _140_2063 = (FStar_Absyn_Print.sli d)
in (FStar_Util.format1 "data constructor proxy: %s" _140_2063))
in Some (_140_2064))
in (ddtok, [], FStar_ToSMT_Term.Term_sort, _140_2065))
in FStar_ToSMT_Term.DeclFun (_140_2066))
in (_140_2067)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _140_2068))
in (FStar_List.append _140_2069 proxy_fresh))
in (FStar_List.append _140_2070 decls_formals))
in (FStar_List.append _140_2071 decls_pred))
in (let _140_2085 = (let _140_2084 = (let _140_2083 = (let _140_2075 = (let _140_2074 = (let _140_2073 = (let _140_2072 = (FStar_ToSMT_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _140_2072))
in (FStar_ToSMT_Term.mkForall _140_2073))
in (_140_2074, Some ("equality for proxy")))
in FStar_ToSMT_Term.Assume (_140_2075))
in (let _140_2082 = (let _140_2081 = (let _140_2080 = (let _140_2079 = (let _140_2078 = (let _140_2077 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) vars')
in (let _140_2076 = (FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _140_2077, _140_2076)))
in (FStar_ToSMT_Term.mkForall _140_2078))
in (_140_2079, Some ("data constructor typing intro")))
in FStar_ToSMT_Term.Assume (_140_2080))
in (_140_2081)::[])
in (_140_2083)::_140_2082))
in (FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_140_2084)
in (FStar_List.append _140_2086 _140_2085)))
in (FStar_List.append _140_2087 elim))
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
| FStar_Absyn_Syntax.Sig_bundle (ses, _50_2796, _50_2798, _50_2800) -> begin
(

let _50_2805 = (encode_signature env ses)
in (match (_50_2805) with
| (g, env) -> begin
(

let _50_2817 = (FStar_All.pipe_right g (FStar_List.partition (fun _50_23 -> (match (_50_23) with
| FStar_ToSMT_Term.Assume (_50_2808, Some ("inversion axiom")) -> begin
false
end
| _50_2814 -> begin
true
end))))
in (match (_50_2817) with
| (g', inversions) -> begin
(

let _50_2826 = (FStar_All.pipe_right g' (FStar_List.partition (fun _50_24 -> (match (_50_24) with
| FStar_ToSMT_Term.DeclFun (_50_2820) -> begin
true
end
| _50_2823 -> begin
false
end))))
in (match (_50_2826) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_let (_50_2828, _50_2830, _50_2832, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _50_25 -> (match (_50_25) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _50_2844 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_let ((is_rec, bindings), _50_2849, _50_2851, quals) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _50_2863 = (FStar_Util.first_N nbinders formals)
in (match (_50_2863) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun formal binder -> (match (((Prims.fst formal), (Prims.fst binder))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _140_2102 = (let _140_2101 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _140_2101))
in FStar_Util.Inl (_140_2102))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _140_2104 = (let _140_2103 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _140_2103))
in FStar_Util.Inr (_140_2104))
end
| _50_2877 -> begin
(FStar_All.failwith "Impossible")
end)) formals binders)
in (

let extra_formals = (let _140_2105 = (FStar_Absyn_Util.subst_binders subst extra_formals)
in (FStar_All.pipe_right _140_2105 FStar_Absyn_Util.name_binders))
in (

let body = (let _140_2111 = (let _140_2107 = (let _140_2106 = (FStar_Absyn_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _140_2106))
in (body, _140_2107))
in (let _140_2110 = (let _140_2109 = (FStar_Absyn_Util.subst_typ subst t)
in (FStar_All.pipe_left (fun _140_2108 -> Some (_140_2108)) _140_2109))
in (FStar_Absyn_Syntax.mk_Exp_app_flat _140_2111 _140_2110 body.FStar_Absyn_Syntax.pos)))
in ((FStar_List.append binders extra_formals), body))))
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

let _50_2915 = (FStar_Util.first_N nformals binders)
in (match (_50_2915) with
| (bs0, rest) -> begin
(

let tres = (match ((FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tres)
end
| _50_2919 -> begin
(FStar_All.failwith "impossible")
end)
in (

let body = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (tres)) body.FStar_Absyn_Syntax.pos)
in (bs0, body, bs0, tres)))
end))
end else begin
if (nformals > nbinders) then begin
(

let _50_2924 = (eta_expand binders formals body tres)
in (match (_50_2924) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end
| _50_2926 -> begin
(let _140_2120 = (let _140_2119 = (FStar_Absyn_Print.exp_to_string e)
in (let _140_2118 = (FStar_Absyn_Print.typ_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _140_2119 _140_2118)))
in (FStar_All.failwith _140_2120))
end)
end
| _50_2928 -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(

let tres = (FStar_Absyn_Util.comp_result c)
in (

let _50_2936 = (eta_expand [] formals e tres)
in (match (_50_2936) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _50_2938 -> begin
([], e, [], t_norm)
end)
end))
in try
(match (()) with
| () -> begin
if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _50_26 -> (match (_50_26) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _50_2951 -> begin
false
end)))) || (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp))))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(

let _50_2970 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _50_2957 lb -> (match (_50_2957) with
| (toks, typs, decls, env) -> begin
(

let _50_2959 = if (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (let _140_2126 = (whnf env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_right _140_2126 FStar_Absyn_Util.compress_typ))
in (

let _50_2965 = (let _140_2127 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _140_2127 lb.FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_50_2965) with
| (tok, decl, env) -> begin
(let _140_2130 = (let _140_2129 = (let _140_2128 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (_140_2128, tok))
in (_140_2129)::toks)
in (_140_2130, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_50_2970) with
| (toks, typs, decls, env) -> begin
(

let toks = (FStar_List.rev toks)
in (

let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _50_27 -> (match (_50_27) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _50_2977 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> ((FStar_Absyn_Util.is_lemma t) || (let _140_2133 = (FStar_Absyn_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _140_2133))))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| (({FStar_Absyn_Syntax.lbname = _50_2985; FStar_Absyn_Syntax.lbtyp = _50_2983; FStar_Absyn_Syntax.lbeff = _50_2981; FStar_Absyn_Syntax.lbdef = e})::[], (t_norm)::[], ((flid, (f, ftok)))::[]) -> begin
(

let _50_3001 = (destruct_bound_function flid t_norm e)
in (match (_50_3001) with
| (binders, body, formals, tres) -> begin
(

let _50_3008 = (encode_binders None binders env)
in (match (_50_3008) with
| (vars, guards, env', binder_decls, _50_3007) -> begin
(

let app = (match (vars) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
end
| _50_3011 -> begin
(let _140_2135 = (let _140_2134 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (f, _140_2134))
in (FStar_ToSMT_Term.mkApp _140_2135))
end)
in (

let _50_3015 = (encode_exp body env')
in (match (_50_3015) with
| (body, decls2) -> begin
(

let eqn = (let _140_2144 = (let _140_2143 = (let _140_2140 = (let _140_2139 = (let _140_2138 = (let _140_2137 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _140_2136 = (FStar_ToSMT_Term.mkEq (app, body))
in (_140_2137, _140_2136)))
in (FStar_ToSMT_Term.mkImp _140_2138))
in (((app)::[])::[], vars, _140_2139))
in (FStar_ToSMT_Term.mkForall _140_2140))
in (let _140_2142 = (let _140_2141 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_140_2141))
in (_140_2143, _140_2142)))
in FStar_ToSMT_Term.Assume (_140_2144))
in ((FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end))
end
| _50_3018 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _140_2145 = (varops.fresh "fuel")
in (_140_2145, FStar_ToSMT_Term.Fuel_sort))
in (

let fuel_tm = (FStar_ToSMT_Term.mkFreeV fuel)
in (

let env0 = env
in (

let _50_3035 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _50_3024 _50_3029 -> (match ((_50_3024, _50_3029)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(

let g = (varops.new_fvar flid)
in (

let gtok = (varops.new_fvar flid)
in (

let env = (let _140_2150 = (let _140_2149 = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _140_2148 -> Some (_140_2148)) _140_2149))
in (push_free_var env flid gtok _140_2150))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_50_3035) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _50_3044 t_norm _50_3053 -> (match ((_50_3044, _50_3053)) with
| ((flid, f, ftok, g, gtok), {FStar_Absyn_Syntax.lbname = _50_3052; FStar_Absyn_Syntax.lbtyp = _50_3050; FStar_Absyn_Syntax.lbeff = _50_3048; FStar_Absyn_Syntax.lbdef = e}) -> begin
(

let _50_3058 = (destruct_bound_function flid t_norm e)
in (match (_50_3058) with
| (binders, body, formals, tres) -> begin
(

let _50_3065 = (encode_binders None binders env)
in (match (_50_3065) with
| (vars, guards, env', binder_decls, _50_3064) -> begin
(

let decl_g = (let _140_2161 = (let _140_2160 = (let _140_2159 = (FStar_List.map Prims.snd vars)
in (FStar_ToSMT_Term.Fuel_sort)::_140_2159)
in (g, _140_2160, FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_ToSMT_Term.DeclFun (_140_2161))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_ToSMT_Term.DeclFun ((gtok, [], FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (

let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (

let app = (FStar_ToSMT_Term.mkApp (f, vars_tm))
in (

let gsapp = (let _140_2164 = (let _140_2163 = (let _140_2162 = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_140_2162)::vars_tm)
in (g, _140_2163))
in (FStar_ToSMT_Term.mkApp _140_2164))
in (

let gmax = (let _140_2167 = (let _140_2166 = (let _140_2165 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_140_2165)::vars_tm)
in (g, _140_2166))
in (FStar_ToSMT_Term.mkApp _140_2167))
in (

let _50_3075 = (encode_exp body env')
in (match (_50_3075) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _140_2176 = (let _140_2175 = (let _140_2172 = (let _140_2171 = (let _140_2170 = (let _140_2169 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _140_2168 = (FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_140_2169, _140_2168)))
in (FStar_ToSMT_Term.mkImp _140_2170))
in (((gsapp)::[])::[], (fuel)::vars, _140_2171))
in (FStar_ToSMT_Term.mkForall _140_2172))
in (let _140_2174 = (let _140_2173 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_140_2173))
in (_140_2175, _140_2174)))
in FStar_ToSMT_Term.Assume (_140_2176))
in (

let eqn_f = (let _140_2180 = (let _140_2179 = (let _140_2178 = (let _140_2177 = (FStar_ToSMT_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _140_2177))
in (FStar_ToSMT_Term.mkForall _140_2178))
in (_140_2179, Some ("Correspondence of recursive function to instrumented version")))
in FStar_ToSMT_Term.Assume (_140_2180))
in (

let eqn_g' = (let _140_2189 = (let _140_2188 = (let _140_2187 = (let _140_2186 = (let _140_2185 = (let _140_2184 = (let _140_2183 = (let _140_2182 = (let _140_2181 = (FStar_ToSMT_Term.n_fuel 0)
in (_140_2181)::vars_tm)
in (g, _140_2182))
in (FStar_ToSMT_Term.mkApp _140_2183))
in (gsapp, _140_2184))
in (FStar_ToSMT_Term.mkEq _140_2185))
in (((gsapp)::[])::[], (fuel)::vars, _140_2186))
in (FStar_ToSMT_Term.mkForall _140_2187))
in (_140_2188, Some ("Fuel irrelevance")))
in FStar_ToSMT_Term.Assume (_140_2189))
in (

let _50_3098 = (

let _50_3085 = (encode_binders None formals env0)
in (match (_50_3085) with
| (vars, v_guards, env, binder_decls, _50_3084) -> begin
(

let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (

let gapp = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (

let tok_corr = (

let tok_app = (let _140_2190 = (FStar_ToSMT_Term.mkFreeV (gtok, FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _140_2190 ((fuel)::vars)))
in (let _140_2194 = (let _140_2193 = (let _140_2192 = (let _140_2191 = (FStar_ToSMT_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _140_2191))
in (FStar_ToSMT_Term.mkForall _140_2192))
in (_140_2193, Some ("Fuel token correspondence")))
in FStar_ToSMT_Term.Assume (_140_2194)))
in (

let _50_3095 = (

let _50_3092 = (encode_typ_pred None tres env gapp)
in (match (_50_3092) with
| (g_typing, d3) -> begin
(let _140_2202 = (let _140_2201 = (let _140_2200 = (let _140_2199 = (let _140_2198 = (let _140_2197 = (let _140_2196 = (let _140_2195 = (FStar_ToSMT_Term.mk_and_l v_guards)
in (_140_2195, g_typing))
in (FStar_ToSMT_Term.mkImp _140_2196))
in (((gapp)::[])::[], (fuel)::vars, _140_2197))
in (FStar_ToSMT_Term.mkForall _140_2198))
in (_140_2199, None))
in FStar_ToSMT_Term.Assume (_140_2200))
in (_140_2201)::[])
in (d3, _140_2202))
end))
in (match (_50_3095) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_50_3098) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (

let _50_3114 = (let _140_2205 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _50_3102 _50_3106 -> (match ((_50_3102, _50_3106)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _50_3110 = (encode_one_binding env0 gtok ty bs)
in (match (_50_3110) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _140_2205))
in (match (_50_3114) with
| (decls, eqns, env0) -> begin
(

let _50_3123 = (let _140_2207 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _140_2207 (FStar_List.partition (fun _50_28 -> (match (_50_28) with
| FStar_ToSMT_Term.DeclFun (_50_3117) -> begin
true
end
| _50_3120 -> begin
false
end)))))
in (match (_50_3123) with
| (prefix_decls, rest) -> begin
(

let eqns = (FStar_List.rev eqns)
in ((FStar_List.append (FStar_List.append prefix_decls rest) eqns), env0))
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

let msg = (let _140_2210 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname))))
in (FStar_All.pipe_right _140_2210 (FStar_String.concat " and ")))
in (

let decl = FStar_ToSMT_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end))
end
| (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end)))))
and declare_top_level_let : env_t  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((Prims.string * FStar_ToSMT_Term.term Prims.option) * FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (match ((try_lookup_lid env x)) with
| None -> begin
(

let _50_3150 = (encode_free_var env x t t_norm [])
in (match (_50_3150) with
| (decls, env) -> begin
(

let _50_3155 = (lookup_lid env x)
in (match (_50_3155) with
| (n, x', _50_3154) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _50_3159) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_ToSMT_Term.decl Prims.list = (fun env lid t -> (

let _50_3167 = (encode_function_type_as_formula None None t env)
in (match (_50_3167) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_ToSMT_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)))))::[]))
end)))
and encode_free_var : env_t  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.qualifier Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env lid tt t_norm quals -> if ((let _140_2223 = (FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _140_2223)) || (FStar_Absyn_Util.is_lemma t_norm)) then begin
(

let _50_3176 = (new_term_constant_and_tok_from_lid env lid)
in (match (_50_3176) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _50_3179) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _50_29 -> (match (_50_29) with
| (FStar_Util.Inl (_50_3184), _50_3187) -> begin
FStar_ToSMT_Term.Type_sort
end
| _50_3190 -> begin
FStar_ToSMT_Term.Term_sort
end))))
end
| _50_3192 -> begin
[]
end)
in (

let d = FStar_ToSMT_Term.DeclFun ((vname, arg_sorts, FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (

let dd = FStar_ToSMT_Term.DeclFun ((vtok, [], FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(

let vname = (varops.new_fvar lid)
in (

let definition = (prims.mk lid vname)
in (

let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let _50_3209 = (match ((FStar_Absyn_Util.function_formals t_norm)) with
| Some (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _140_2225 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _140_2225))
end else begin
(args, (None, (FStar_Absyn_Util.comp_result comp)))
end
end
| None -> begin
([], (None, t_norm))
end)
in (match (_50_3209) with
| (formals, (pre_opt, res_t)) -> begin
(

let _50_3213 = (new_term_constant_and_tok_from_lid env lid)
in (match (_50_3213) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
end
| _50_3216 -> begin
(FStar_ToSMT_Term.mkApp (vtok, []))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _50_30 -> (match (_50_30) with
| FStar_Absyn_Syntax.Discriminator (d) -> begin
(

let _50_3232 = (FStar_Util.prefix vars)
in (match (_50_3232) with
| (_50_3227, (xxsym, _50_3230)) -> begin
(

let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (let _140_2242 = (let _140_2241 = (let _140_2240 = (let _140_2239 = (let _140_2238 = (let _140_2237 = (let _140_2236 = (let _140_2235 = (FStar_ToSMT_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _140_2235))
in (vapp, _140_2236))
in (FStar_ToSMT_Term.mkEq _140_2237))
in (((vapp)::[])::[], vars, _140_2238))
in (FStar_ToSMT_Term.mkForall _140_2239))
in (_140_2240, Some ("Discriminator equation")))
in FStar_ToSMT_Term.Assume (_140_2241))
in (_140_2242)::[]))
end))
end
| FStar_Absyn_Syntax.Projector (d, FStar_Util.Inr (f)) -> begin
(

let _50_3245 = (FStar_Util.prefix vars)
in (match (_50_3245) with
| (_50_3240, (xxsym, _50_3243)) -> begin
(

let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (

let prim_app = (let _140_2244 = (let _140_2243 = (mk_term_projector_name d f)
in (_140_2243, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _140_2244))
in (let _140_2249 = (let _140_2248 = (let _140_2247 = (let _140_2246 = (let _140_2245 = (FStar_ToSMT_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _140_2245))
in (FStar_ToSMT_Term.mkForall _140_2246))
in (_140_2247, Some ("Projector equation")))
in FStar_ToSMT_Term.Assume (_140_2248))
in (_140_2249)::[])))
end))
end
| _50_3249 -> begin
[]
end)))))
in (

let _50_3256 = (encode_binders None formals env)
in (match (_50_3256) with
| (vars, guards, env', decls1, _50_3255) -> begin
(

let _50_3265 = (match (pre_opt) with
| None -> begin
(let _140_2250 = (FStar_ToSMT_Term.mk_and_l guards)
in (_140_2250, decls1))
end
| Some (p) -> begin
(

let _50_3262 = (encode_formula p env')
in (match (_50_3262) with
| (g, ds) -> begin
(let _140_2251 = (FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_140_2251, (FStar_List.append decls1 ds)))
end))
end)
in (match (_50_3265) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_ApplyE vtok_tm vars)
in (

let vapp = (let _140_2253 = (let _140_2252 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (vname, _140_2252))
in (FStar_ToSMT_Term.mkApp _140_2253))
in (

let _50_3296 = (

let vname_decl = (let _140_2256 = (let _140_2255 = (FStar_All.pipe_right formals (FStar_List.map (fun _50_31 -> (match (_50_31) with
| (FStar_Util.Inl (_50_3270), _50_3273) -> begin
FStar_ToSMT_Term.Type_sort
end
| _50_3276 -> begin
FStar_ToSMT_Term.Term_sort
end))))
in (vname, _140_2255, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_140_2256))
in (

let _50_3283 = (

let env = (

let _50_3278 = env
in {bindings = _50_3278.bindings; depth = _50_3278.depth; tcenv = _50_3278.tcenv; warn = _50_3278.warn; cache = _50_3278.cache; nolabels = _50_3278.nolabels; use_zfuel_name = _50_3278.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_typ_pred None tt env vtok_tm)
end else begin
(encode_typ_pred None t_norm env vtok_tm)
end)
in (match (_50_3283) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in (

let _50_3293 = (match (formals) with
| [] -> begin
(let _140_2260 = (let _140_2259 = (let _140_2258 = (FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
in (FStar_All.pipe_left (fun _140_2257 -> Some (_140_2257)) _140_2258))
in (push_free_var env lid vname _140_2259))
in ((FStar_List.append decls2 ((tok_typing)::[])), _140_2260))
end
| _50_3287 -> begin
(

let vtok_decl = FStar_ToSMT_Term.DeclFun ((vtok, [], FStar_ToSMT_Term.Term_sort, None))
in (

let vtok_fresh = (let _140_2261 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (vtok, FStar_ToSMT_Term.Term_sort) _140_2261))
in (

let name_tok_corr = (let _140_2265 = (let _140_2264 = (let _140_2263 = (let _140_2262 = (FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _140_2262))
in (FStar_ToSMT_Term.mkForall _140_2263))
in (_140_2264, None))
in FStar_ToSMT_Term.Assume (_140_2265))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_50_3293) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_50_3296) with
| (decls2, env) -> begin
(

let _50_3304 = (

let res_t = (FStar_Absyn_Util.compress_typ res_t)
in (

let _50_3300 = (encode_typ_term res_t env')
in (match (_50_3300) with
| (encoded_res_t, decls) -> begin
(let _140_2266 = (FStar_ToSMT_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _140_2266, decls))
end)))
in (match (_50_3304) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _140_2270 = (let _140_2269 = (let _140_2268 = (let _140_2267 = (FStar_ToSMT_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _140_2267))
in (FStar_ToSMT_Term.mkForall _140_2268))
in (_140_2269, Some ("free var typing")))
in FStar_ToSMT_Term.Assume (_140_2270))
in (

let g = (let _140_2272 = (let _140_2271 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_140_2271)
in (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) _140_2272))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end
end)
and encode_signature : env_t  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _50_3311 se -> (match (_50_3311) with
| (g, env) -> begin
(

let _50_3315 = (encode_sigelt env se)
in (match (_50_3315) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))


let encode_env_bindings : env_t  ->  FStar_Tc_Env.binding Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env bindings -> (

let encode_binding = (fun b _50_3322 -> (match (_50_3322) with
| (decls, env) -> begin
(match (b) with
| FStar_Tc_Env.Binding_var (x, t0) -> begin
(

let _50_3330 = (new_term_constant env x)
in (match (_50_3330) with
| (xxsym, xx, env') -> begin
(

let t1 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (

let _50_3332 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _140_2287 = (FStar_Absyn_Print.strBvd x)
in (let _140_2286 = (FStar_Absyn_Print.typ_to_string t0)
in (let _140_2285 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _140_2287 _140_2286 _140_2285))))
end else begin
()
end
in (

let _50_3336 = (encode_typ_pred None t1 env xx)
in (match (_50_3336) with
| (t, decls') -> begin
(

let caption = if (FStar_Options.log_queries ()) then begin
(let _140_2291 = (let _140_2290 = (FStar_Absyn_Print.strBvd x)
in (let _140_2289 = (FStar_Absyn_Print.typ_to_string t0)
in (let _140_2288 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _140_2290 _140_2289 _140_2288))))
in Some (_140_2291))
end else begin
None
end
in (

let g = (FStar_List.append (FStar_List.append ((FStar_ToSMT_Term.DeclFun ((xxsym, [], FStar_ToSMT_Term.Term_sort, caption)))::[]) decls') ((FStar_ToSMT_Term.Assume ((t, None)))::[]))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(

let _50_3346 = (new_typ_constant env a)
in (match (_50_3346) with
| (aasym, aa, env') -> begin
(

let _50_3349 = (encode_knd k env aa)
in (match (_50_3349) with
| (k, decls') -> begin
(

let g = (let _140_2297 = (let _140_2296 = (let _140_2295 = (let _140_2294 = (let _140_2293 = (let _140_2292 = (FStar_Absyn_Print.strBvd a)
in Some (_140_2292))
in (aasym, [], FStar_ToSMT_Term.Type_sort, _140_2293))
in FStar_ToSMT_Term.DeclFun (_140_2294))
in (_140_2295)::[])
in (FStar_List.append _140_2296 decls'))
in (FStar_List.append _140_2297 ((FStar_ToSMT_Term.Assume ((k, None)))::[])))
in ((FStar_List.append decls g), env'))
end))
end))
end
| FStar_Tc_Env.Binding_lid (x, t) -> begin
(

let t_norm = (whnf env t)
in (

let _50_3358 = (encode_free_var env x t t_norm [])
in (match (_50_3358) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end)))
end
| FStar_Tc_Env.Binding_sig (se) -> begin
(

let _50_3363 = (encode_sigelt env se)
in (match (_50_3363) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _50_3370 -> (match (_50_3370) with
| (l, _50_3367, _50_3369) -> begin
FStar_ToSMT_Term.DeclFun (((Prims.fst l), [], FStar_ToSMT_Term.Bool_sort, None))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _50_3377 -> (match (_50_3377) with
| (l, _50_3374, _50_3376) -> begin
(let _140_2305 = (FStar_All.pipe_left (fun _140_2301 -> FStar_ToSMT_Term.Echo (_140_2301)) (Prims.fst l))
in (let _140_2304 = (let _140_2303 = (let _140_2302 = (FStar_ToSMT_Term.mkFreeV l)
in FStar_ToSMT_Term.Eval (_140_2302))
in (_140_2303)::[])
in (_140_2305)::_140_2304))
end))))
in (prefix, suffix))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_Tc_Env.env  ->  Prims.unit = (fun tcenv -> (let _140_2310 = (let _140_2309 = (let _140_2308 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _140_2308; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_140_2309)::[])
in (FStar_ST.op_Colon_Equals last_env _140_2310)))


let get_env : FStar_Tc_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_50_3383 -> begin
(

let _50_3386 = e
in {bindings = _50_3386.bindings; depth = _50_3386.depth; tcenv = tcenv; warn = _50_3386.warn; cache = _50_3386.cache; nolabels = _50_3386.nolabels; use_zfuel_name = _50_3386.use_zfuel_name; encode_non_total_function_typ = _50_3386.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_50_3392)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _50_3394 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (hd)::tl -> begin
(

let refs = (FStar_Util.smap_copy hd.cache)
in (

let top = (

let _50_3400 = hd
in {bindings = _50_3400.bindings; depth = _50_3400.depth; tcenv = _50_3400.tcenv; warn = _50_3400.warn; cache = refs; nolabels = _50_3400.nolabels; use_zfuel_name = _50_3400.use_zfuel_name; encode_non_total_function_typ = _50_3400.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _50_3403 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_50_3407)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _50_3409 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _50_3410 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _50_3411 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_50_3414)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _50_3419 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_Tc_Env.env  ->  Prims.unit = (fun tcenv -> (

let _50_3421 = (init_env tcenv)
in (

let _50_3423 = (FStar_ToSMT_Z3.init ())
in (FStar_ToSMT_Z3.giveZ3 ((FStar_ToSMT_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _50_3426 = (push_env ())
in (

let _50_3428 = (varops.push ())
in (FStar_ToSMT_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _50_3431 = (let _140_2331 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _140_2331))
in (

let _50_3433 = (varops.pop ())
in (FStar_ToSMT_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _50_3436 = (mark_env ())
in (

let _50_3438 = (varops.mark ())
in (FStar_ToSMT_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _50_3441 = (reset_mark_env ())
in (

let _50_3443 = (varops.reset_mark ())
in (FStar_ToSMT_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _50_3446 = (commit_mark_env ())
in (

let _50_3448 = (varops.commit_mark ())
in (FStar_ToSMT_Z3.commit_mark msg))))


let encode_sig : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _140_2345 = (let _140_2344 = (let _140_2343 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (Prims.strcat "encoding sigelt " _140_2343))
in FStar_ToSMT_Term.Caption (_140_2344))
in (_140_2345)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _50_3457 = (encode_sigelt env se)
in (match (_50_3457) with
| (decls, env) -> begin
(

let _50_3458 = (set_env env)
in (let _140_2346 = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 _140_2346)))
end)))))


let encode_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Ident.str)
in (

let _50_3463 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _140_2351 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Absyn_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "Encoding externals for %s ... %s exports\n" name _140_2351))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _50_3470 = (encode_signature (

let _50_3466 = env
in {bindings = _50_3466.bindings; depth = _50_3466.depth; tcenv = _50_3466.tcenv; warn = false; cache = _50_3466.cache; nolabels = _50_3466.nolabels; use_zfuel_name = _50_3466.use_zfuel_name; encode_non_total_function_typ = _50_3466.encode_non_total_function_typ}) modul.FStar_Absyn_Syntax.exports)
in (match (_50_3470) with
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

let _50_3476 = (set_env (

let _50_3474 = env
in {bindings = _50_3474.bindings; depth = _50_3474.depth; tcenv = _50_3474.tcenv; warn = true; cache = _50_3474.cache; nolabels = _50_3474.nolabels; use_zfuel_name = _50_3474.use_zfuel_name; encode_non_total_function_typ = _50_3474.encode_non_total_function_typ}))
in (

let _50_3478 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (

let decls = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))


let solve : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun tcenv q -> (

let _50_3483 = (let _140_2360 = (let _140_2359 = (let _140_2358 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _140_2358))
in (FStar_Util.format1 "Starting query at %s" _140_2359))
in (push _140_2360))
in (

let pop = (fun _50_3486 -> (match (()) with
| () -> begin
(let _140_2365 = (let _140_2364 = (let _140_2363 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _140_2363))
in (FStar_Util.format1 "Ending query at %s" _140_2364))
in (pop _140_2365))
end))
in (

let _50_3545 = (

let env = (get_env tcenv)
in (

let bindings = (FStar_Tc_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let _50_3519 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_Tc_Env.Binding_var (x, t))::rest -> begin
(

let _50_3501 = (aux rest)
in (match (_50_3501) with
| (out, rest) -> begin
(

let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
in (let _140_2371 = (let _140_2370 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_140_2370)::out)
in (_140_2371, rest)))
end))
end
| (FStar_Tc_Env.Binding_typ (a, k))::rest -> begin
(

let _50_3511 = (aux rest)
in (match (_50_3511) with
| (out, rest) -> begin
(let _140_2373 = (let _140_2372 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_140_2372)::out)
in (_140_2373, rest))
end))
end
| _50_3513 -> begin
([], bindings)
end))
in (

let _50_3516 = (aux bindings)
in (match (_50_3516) with
| (closing, bindings) -> begin
(let _140_2374 = (FStar_Absyn_Util.close_forall (FStar_List.rev closing) q)
in (_140_2374, bindings))
end)))
in (match (_50_3519) with
| (q, bindings) -> begin
(

let _50_3528 = (let _140_2376 = (FStar_List.filter (fun _50_32 -> (match (_50_32) with
| FStar_Tc_Env.Binding_sig (_50_3522) -> begin
false
end
| _50_3525 -> begin
true
end)) bindings)
in (encode_env_bindings env _140_2376))
in (match (_50_3528) with
| (env_decls, env) -> begin
(

let _50_3529 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _140_2377 = (FStar_Absyn_Print.formula_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _140_2377))
end else begin
()
end
in (

let _50_3534 = (encode_formula_with_labels q env)
in (match (_50_3534) with
| (phi, labels, qdecls) -> begin
(

let _50_3537 = (encode_labels labels)
in (match (_50_3537) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (

let qry = (let _140_2379 = (let _140_2378 = (FStar_ToSMT_Term.mkNot phi)
in (_140_2378, Some ("query")))
in FStar_ToSMT_Term.Assume (_140_2379))
in (

let suffix = (FStar_List.append label_suffix ((FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))
end))))
in (match (_50_3545) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_ToSMT_Term.Assume ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (FStar_ToSMT_Term.False, _50_3552); FStar_ToSMT_Term.hash = _50_3549; FStar_ToSMT_Term.freevars = _50_3547}, _50_3557) -> begin
(

let _50_3560 = (pop ())
in ())
end
| _50_3563 when tcenv.FStar_Tc_Env.admit -> begin
(

let _50_3564 = (pop ())
in ())
end
| FStar_ToSMT_Term.Assume (q, _50_3568) -> begin
(

let fresh = ((FStar_String.length q.FStar_ToSMT_Term.hash) >= 2048)
in (

let _50_3572 = (FStar_ToSMT_Z3.giveZ3 prefix)
in (

let with_fuel = (fun p _50_3578 -> (match (_50_3578) with
| (n, i) -> begin
(let _140_2402 = (let _140_2401 = (let _140_2386 = (let _140_2385 = (FStar_Util.string_of_int n)
in (let _140_2384 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _140_2385 _140_2384)))
in FStar_ToSMT_Term.Caption (_140_2386))
in (let _140_2400 = (let _140_2399 = (let _140_2391 = (let _140_2390 = (let _140_2389 = (let _140_2388 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _140_2387 = (FStar_ToSMT_Term.n_fuel n)
in (_140_2388, _140_2387)))
in (FStar_ToSMT_Term.mkEq _140_2389))
in (_140_2390, None))
in FStar_ToSMT_Term.Assume (_140_2391))
in (let _140_2398 = (let _140_2397 = (let _140_2396 = (let _140_2395 = (let _140_2394 = (let _140_2393 = (FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _140_2392 = (FStar_ToSMT_Term.n_fuel i)
in (_140_2393, _140_2392)))
in (FStar_ToSMT_Term.mkEq _140_2394))
in (_140_2395, None))
in FStar_ToSMT_Term.Assume (_140_2396))
in (_140_2397)::(p)::(FStar_ToSMT_Term.CheckSat)::[])
in (_140_2399)::_140_2398))
in (_140_2401)::_140_2400))
in (FStar_List.append _140_2402 suffix))
end))
in (

let check = (fun p -> (

let initial_config = (let _140_2406 = (FStar_Options.initial_fuel ())
in (let _140_2405 = (FStar_Options.initial_ifuel ())
in (_140_2406, _140_2405)))
in (

let alt_configs = (let _140_2425 = (let _140_2424 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _140_2409 = (let _140_2408 = (FStar_Options.initial_fuel ())
in (let _140_2407 = (FStar_Options.max_ifuel ())
in (_140_2408, _140_2407)))
in (_140_2409)::[])
end else begin
[]
end
in (let _140_2423 = (let _140_2422 = if (((FStar_Options.max_fuel ()) / 2) > (FStar_Options.initial_fuel ())) then begin
(let _140_2412 = (let _140_2411 = ((FStar_Options.max_fuel ()) / 2)
in (let _140_2410 = (FStar_Options.max_ifuel ())
in (_140_2411, _140_2410)))
in (_140_2412)::[])
end else begin
[]
end
in (let _140_2421 = (let _140_2420 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _140_2415 = (let _140_2414 = (FStar_Options.max_fuel ())
in (let _140_2413 = (FStar_Options.max_ifuel ())
in (_140_2414, _140_2413)))
in (_140_2415)::[])
end else begin
[]
end
in (let _140_2419 = (let _140_2418 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _140_2417 = (let _140_2416 = (FStar_Options.min_fuel ())
in (_140_2416, 1))
in (_140_2417)::[])
end else begin
[]
end
in (_140_2418)::[])
in (_140_2420)::_140_2419))
in (_140_2422)::_140_2421))
in (_140_2424)::_140_2423))
in (FStar_List.flatten _140_2425))
in (

let report = (fun errs -> (

let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Absyn_Syntax.dummyRange))::[]
end
| _50_3587 -> begin
errs
end)
in (

let _50_3589 = if (FStar_Options.print_fuels ()) then begin
(let _140_2433 = (let _140_2428 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _140_2428))
in (let _140_2432 = (let _140_2429 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _140_2429 FStar_Util.string_of_int))
in (let _140_2431 = (let _140_2430 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _140_2430 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _140_2433 _140_2432 _140_2431))))
end else begin
()
end
in (FStar_Tc_Errors.add_errors tcenv errs))))
in (

let rec try_alt_configs = (fun p errs _50_33 -> (match (_50_33) with
| [] -> begin
(report errs)
end
| (mi)::[] -> begin
(match (errs) with
| [] -> begin
(let _140_2444 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _140_2444 (cb mi p [])))
end
| _50_3601 -> begin
(report errs)
end)
end
| (mi)::tl -> begin
(let _140_2446 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _140_2446 (fun _50_3607 -> (match (_50_3607) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _50_3610 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _50_3613 p alt _50_3618 -> (match ((_50_3613, _50_3618)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_Options.print_fuels ()) then begin
(let _140_2454 = (let _140_2451 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _140_2451))
in (let _140_2453 = (FStar_Util.string_of_int prev_fuel)
in (let _140_2452 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _140_2454 _140_2453 _140_2452))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _140_2455 = (with_fuel p initial_config)
in (FStar_ToSMT_Z3.ask fresh labels _140_2455 (cb initial_config p alt_configs))))))))
in (

let process_query = (fun q -> if ((FStar_Options.split_cases ()) > 0) then begin
(

let _50_3623 = (let _140_2461 = (FStar_Options.split_cases ())
in (FStar_ToSMT_SplitQueryCases.can_handle_query _140_2461 q))
in (match (_50_3623) with
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

let _50_3624 = if (FStar_Options.admit_smt_queries ()) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end)
end)))))


let is_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (

let env = (get_env tcenv)
in (

let _50_3629 = (push "query")
in (

let _50_3636 = (encode_formula_with_labels q env)
in (match (_50_3636) with
| (f, _50_3633, _50_3635) -> begin
(

let _50_3637 = (pop "query")
in (match (f.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _50_3641) -> begin
true
end
| _50_3645 -> begin
false
end))
end)))))


let solver : FStar_Tc_Env.solver_t = {FStar_Tc_Env.init = init; FStar_Tc_Env.push = push; FStar_Tc_Env.pop = pop; FStar_Tc_Env.mark = mark; FStar_Tc_Env.reset_mark = reset_mark; FStar_Tc_Env.commit_mark = commit_mark; FStar_Tc_Env.encode_modul = encode_modul; FStar_Tc_Env.encode_sig = encode_sig; FStar_Tc_Env.solve = solve; FStar_Tc_Env.is_trivial = is_trivial; FStar_Tc_Env.finish = FStar_ToSMT_Z3.finish; FStar_Tc_Env.refresh = FStar_ToSMT_Z3.refresh}


let dummy : FStar_Tc_Env.solver_t = {FStar_Tc_Env.init = (fun _50_3646 -> ()); FStar_Tc_Env.push = (fun _50_3648 -> ()); FStar_Tc_Env.pop = (fun _50_3650 -> ()); FStar_Tc_Env.mark = (fun _50_3652 -> ()); FStar_Tc_Env.reset_mark = (fun _50_3654 -> ()); FStar_Tc_Env.commit_mark = (fun _50_3656 -> ()); FStar_Tc_Env.encode_modul = (fun _50_3658 _50_3660 -> ()); FStar_Tc_Env.encode_sig = (fun _50_3662 _50_3664 -> ()); FStar_Tc_Env.solve = (fun _50_3666 _50_3668 -> ()); FStar_Tc_Env.is_trivial = (fun _50_3670 _50_3672 -> false); FStar_Tc_Env.finish = (fun _50_3674 -> ()); FStar_Tc_Env.refresh = (fun _50_3675 -> ())}






open Prims

let add_fuel = (fun x tl -> if (FStar_Options.unthrottle_inductives ()) then begin
tl
end else begin
(x)::tl
end)


let withenv = (fun c _90_31 -> (match (_90_31) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun _90_1 -> (match (_90_1) with
| (FStar_Util.Inl (_90_35), _90_38) -> begin
false
end
| _90_41 -> begin
true
end)) args))


let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l)) -> begin
(let _187_12 = (let _187_11 = (let _187_10 = (let _187_9 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _187_9))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _187_10))
in FStar_Util.Inl (_187_11))
in Some (_187_12))
end
| _90_48 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a = (

let _90_52 = a
in (let _187_19 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _187_19; FStar_Syntax_Syntax.index = _90_52.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _90_52.FStar_Syntax_Syntax.sort}))
in (let _187_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _187_20))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun _90_59 -> (match (()) with
| () -> begin
(let _187_30 = (let _187_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _187_29 lid.FStar_Ident.str))
in (FStar_All.failwith _187_30))
end))
in (

let _90_63 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_90_63) with
| (_90_61, t) -> begin
(match ((let _187_31 = (FStar_Syntax_Subst.compress t)
in _187_31.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _90_71 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_90_71) with
| (binders, _90_70) -> begin
if ((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end
end))
end
| _90_74 -> begin
(fail ())
end)
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _187_37 = (let _187_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _187_36))
in (FStar_All.pipe_left escape _187_37)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _187_43 = (let _187_42 = (mk_term_projector_name lid a)
in ((_187_42), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV _187_43)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _187_49 = (let _187_48 = (mk_term_projector_name_by_pos lid i)
in ((_187_48), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV _187_49)))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))


type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun _90_99 -> (match (()) with
| () -> begin
(let _187_162 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (let _187_161 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((_187_162), (_187_161))))
end))
in (

let scopes = (let _187_164 = (let _187_163 = (new_scope ())
in (_187_163)::[])
in (FStar_Util.mk_ref _187_164))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _187_168 = (FStar_ST.read scopes)
in (FStar_Util.find_map _187_168 (fun _90_107 -> (match (_90_107) with
| (names, _90_106) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_90_110) -> begin
(

let _90_112 = (FStar_Util.incr ctr)
in (let _187_171 = (let _187_170 = (let _187_169 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _187_169))
in (Prims.strcat "__" _187_170))
in (Prims.strcat y _187_171)))
end)
in (

let top_scope = (let _187_173 = (let _187_172 = (FStar_ST.read scopes)
in (FStar_List.hd _187_172))
in (FStar_All.pipe_left Prims.fst _187_173))
in (

let _90_116 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (let _187_180 = (let _187_179 = (let _187_178 = (FStar_Util.string_of_int rn)
in (Prims.strcat "__" _187_178))
in (Prims.strcat pp.FStar_Ident.idText _187_179))
in (FStar_All.pipe_left mk_unique _187_180)))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun _90_124 -> (match (()) with
| () -> begin
(

let _90_125 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (

let fresh = (fun pfx -> (let _187_188 = (let _187_187 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _187_187))
in (FStar_Util.format2 "%s_%s" pfx _187_188)))
in (

let string_const = (fun s -> (match ((let _187_192 = (FStar_ST.read scopes)
in (FStar_Util.find_map _187_192 (fun _90_134 -> (match (_90_134) with
| (_90_132, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _187_193 = (FStar_SMTEncoding_Util.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _187_193))
in (

let top_scope = (let _187_195 = (let _187_194 = (FStar_ST.read scopes)
in (FStar_List.hd _187_194))
in (FStar_All.pipe_left Prims.snd _187_195))
in (

let _90_141 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _90_144 -> (match (()) with
| () -> begin
(let _187_200 = (let _187_199 = (new_scope ())
in (let _187_198 = (FStar_ST.read scopes)
in (_187_199)::_187_198))
in (FStar_ST.op_Colon_Equals scopes _187_200))
end))
in (

let pop = (fun _90_146 -> (match (()) with
| () -> begin
(let _187_204 = (let _187_203 = (FStar_ST.read scopes)
in (FStar_List.tl _187_203))
in (FStar_ST.op_Colon_Equals scopes _187_204))
end))
in (

let mark = (fun _90_148 -> (match (()) with
| () -> begin
(push ())
end))
in (

let reset_mark = (fun _90_150 -> (match (()) with
| () -> begin
(pop ())
end))
in (

let commit_mark = (fun _90_152 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
(

let _90_165 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (

let _90_170 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes ((((next1), (next2)))::tl))))
end
| _90_173 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let _90_175 = x
in (let _187_219 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _187_219; FStar_Syntax_Syntax.index = _90_175.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _90_175.FStar_Syntax_Syntax.sort})))


type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option)


let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
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


let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_90_179) -> begin
_90_179
end))


let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_90_182) -> begin
_90_182
end))


let binder_of_eithervar = (fun v -> ((v), (None)))


type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))


let print_env : env_t  ->  Prims.string = (fun e -> (let _187_277 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _90_2 -> (match (_90_2) with
| Binding_var (x, _90_197) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _90_202, _90_204, _90_206) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _187_277 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _187_287 = (FStar_Syntax_Print.term_to_string t)
in Some (_187_287))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _187_292 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (_187_292)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (let _187_297 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _187_297))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let _90_220 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = _90_220.tcenv; warn = _90_220.warn; cache = _90_220.cache; nolabels = _90_220.nolabels; use_zfuel_name = _90_220.use_zfuel_name; encode_non_total_function_typ = _90_220.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _90_226 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _90_226.depth; tcenv = _90_226.tcenv; warn = _90_226.warn; cache = _90_226.cache; nolabels = _90_226.nolabels; use_zfuel_name = _90_226.use_zfuel_name; encode_non_total_function_typ = _90_226.encode_non_total_function_typ}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _90_233 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _90_233.depth; tcenv = _90_233.tcenv; warn = _90_233.warn; cache = _90_233.cache; nolabels = _90_233.nolabels; use_zfuel_name = _90_233.use_zfuel_name; encode_non_total_function_typ = _90_233.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let _90_238 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = _90_238.depth; tcenv = _90_238.tcenv; warn = _90_238.warn; cache = _90_238.cache; nolabels = _90_238.nolabels; use_zfuel_name = _90_238.use_zfuel_name; encode_non_total_function_typ = _90_238.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun _90_3 -> (match (_90_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some (((b), (t)))
end
| _90_250 -> begin
None
end))))
in (match ((aux a)) with
| None -> begin
(

let a = (unmangle a)
in (match ((aux a)) with
| None -> begin
(let _187_322 = (let _187_321 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found (after unmangling): %s" _187_321))
in (FStar_All.failwith _187_322))
end
| Some (b, t) -> begin
t
end))
end
| Some (b, t) -> begin
t
end)))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (let _187_333 = (

let _90_266 = env
in (let _187_332 = (let _187_331 = (let _187_330 = (let _187_329 = (let _187_328 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _187_327 -> Some (_187_327)) _187_328))
in ((x), (fname), (_187_329), (None)))
in Binding_fvar (_187_330))
in (_187_331)::env.bindings)
in {bindings = _187_332; depth = _90_266.depth; tcenv = _90_266.tcenv; warn = _90_266.warn; cache = _90_266.cache; nolabels = _90_266.nolabels; use_zfuel_name = _90_266.use_zfuel_name; encode_non_total_function_typ = _90_266.encode_non_total_function_typ}))
in ((fname), (ftok), (_187_333))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _90_4 -> (match (_90_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| _90_278 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _187_344 = (lookup_binding env (fun _90_5 -> (match (_90_5) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| _90_289 -> begin
None
end)))
in (FStar_All.pipe_right _187_344 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _187_350 = (let _187_349 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _187_349))
in (FStar_All.failwith _187_350))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _90_299 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = _90_299.depth; tcenv = _90_299.tcenv; warn = _90_299.warn; cache = _90_299.cache; nolabels = _90_299.nolabels; use_zfuel_name = _90_299.use_zfuel_name; encode_non_total_function_typ = _90_299.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _90_308 = (lookup_lid env x)
in (match (_90_308) with
| (t1, t2, _90_307) -> begin
(

let t3 = (let _187_367 = (let _187_366 = (let _187_365 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (_187_365)::[])
in ((f), (_187_366)))
in (FStar_SMTEncoding_Util.mkApp _187_367))
in (

let _90_310 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = _90_310.depth; tcenv = _90_310.tcenv; warn = _90_310.warn; cache = _90_310.cache; nolabels = _90_310.nolabels; use_zfuel_name = _90_310.use_zfuel_name; encode_non_total_function_typ = _90_310.encode_non_total_function_typ}))
end)))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
None
end
| Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
Some (f)
end
| _90_323 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_90_327, (fuel)::[]) -> begin
if (let _187_373 = (let _187_372 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _187_372 Prims.fst))
in (FStar_Util.starts_with _187_373 "fuel")) then begin
(let _187_376 = (let _187_375 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF _187_375 fuel))
in (FStar_All.pipe_left (fun _187_374 -> Some (_187_374)) _187_376))
end else begin
Some (t)
end
end
| _90_333 -> begin
Some (t)
end)
end
| _90_335 -> begin
None
end)
end)
end))


let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _187_380 = (let _187_379 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _187_379))
in (FStar_All.failwith _187_380))
end))


let lookup_free_var_name = (fun env a -> (

let _90_348 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_90_348) with
| (x, _90_345, _90_347) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _90_354 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_90_354) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = _90_358; FStar_SMTEncoding_Term.rng = _90_356}) when env.use_zfuel_name -> begin
((g), (zf))
end
| _90_366 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| _90_376 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _90_6 -> (match (_90_6) with
| Binding_fvar (_90_381, nm', tok, _90_385) when (nm = nm') -> begin
tok
end
| _90_389 -> begin
None
end))))


let mkForall_fuel' = (fun n _90_394 -> (match (_90_394) with
| (pats, vars, body) -> begin
(

let fallback = (fun _90_396 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body)))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _90_399 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_90_399) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| _90_409 -> begin
p
end)))))
in (

let pats = (FStar_List.map add_fuel pats)
in (

let body = (match (body.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (guard)::(body')::[]) -> begin
(

let guard = (match (guard.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, guards) -> begin
(let _187_397 = (add_fuel guards)
in (FStar_SMTEncoding_Util.mk_and_l _187_397))
end
| _90_422 -> begin
(let _187_398 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _187_398 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard), (body'))))
end
| _90_425 -> begin
body
end)
in (

let vars = (((fsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars
in (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body)))))))
end))
end)
end))


let mkForall_fuel : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' (Prims.parse_int "1"))


let head_normal : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_fvar (fv)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _187_404 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _187_404 FStar_Option.isNone))
end
| _90_464 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _187_409 = (FStar_Syntax_Util.un_uinst t)
in _187_409.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_90_468, _90_470, Some (FStar_Util.Inr (l, flags))) -> begin
(((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) || (FStar_List.existsb (fun _90_7 -> (match (_90_7) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| _90_481 -> begin
false
end)) flags))
end
| FStar_Syntax_Syntax.Tm_abs (_90_483, _90_485, Some (FStar_Util.Inl (lc))) -> begin
(FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _187_411 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _187_411 FStar_Option.isSome))
end
| _90_494 -> begin
false
end))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _187_424 = (let _187_422 = (FStar_Syntax_Syntax.null_binder t)
in (_187_422)::[])
in (let _187_423 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _187_424 _187_423 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _187_431 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _187_431))
end
| s -> begin
(

let _90_506 = ()
in (let _187_432 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out _187_432)))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _90_8 -> (match (_90_8) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _90_516 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = _90_527; FStar_SMTEncoding_Term.rng = _90_525})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _90_545) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _90_552 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_90_554, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _90_560 -> begin
None
end))
in (aux t (FStar_List.rev vars))))


type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)


type labels =
label Prims.list


type pattern =
{pat_vars : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t); guard : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term; projections : FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list}


let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))


exception Let_rec_unencodeable


let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable (_) -> begin
true
end
| _ -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _90_9 -> (match (_90_9) with
| FStar_Const.Const_unit -> begin
FStar_SMTEncoding_Term.mk_Term_unit
end
| FStar_Const.Const_bool (true) -> begin
(FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
end
| FStar_Const.Const_bool (false) -> begin
(FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse)
end
| FStar_Const.Const_char (c) -> begin
(let _187_489 = (let _187_488 = (let _187_487 = (let _187_486 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _187_486))
in (_187_487)::[])
in (("FStar.Char.Char"), (_187_488)))
in (FStar_SMTEncoding_Util.mkApp _187_489))
end
| FStar_Const.Const_int (i, None) -> begin
(let _187_490 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _187_490))
end
| FStar_Const.Const_int (i, Some (_90_580)) -> begin
(FStar_All.failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, _90_586) -> begin
(let _187_491 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _187_491))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _187_493 = (let _187_492 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _187_492))
in (FStar_All.failwith _187_493))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_90_600) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_90_603) -> begin
(let _187_502 = (FStar_Syntax_Util.unrefine t)
in (aux true _187_502))
end
| _90_606 -> begin
if norm then begin
(let _187_503 = (whnf env t)
in (aux false _187_503))
end else begin
(let _187_506 = (let _187_505 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _187_504 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _187_505 _187_504)))
in (FStar_All.failwith _187_506))
end
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _90_614 -> begin
(let _187_509 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_187_509)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (

let _90_618 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _187_557 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _187_557))
end else begin
()
end
in (

let _90_646 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _90_625 b -> (match (_90_625) with
| (vars, guards, env, decls, names) -> begin
(

let _90_640 = (

let x = (unmangle (Prims.fst b))
in (

let _90_631 = (gen_term_var env x)
in (match (_90_631) with
| (xxsym, xx, env') -> begin
(

let _90_634 = (let _187_560 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _187_560 env xx))
in (match (_90_634) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (_90_640) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (_90_646) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _90_653 = (encode_term t env)
in (match (_90_653) with
| (t, decls) -> begin
(let _187_565 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_187_565), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _90_660 = (encode_term t env)
in (match (_90_660) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _187_570 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((_187_570), (decls)))
end
| Some (f) -> begin
(let _187_571 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((_187_571), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in (

let _90_667 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _187_576 = (FStar_Syntax_Print.tag_of_term t)
in (let _187_575 = (FStar_Syntax_Print.tag_of_term t0)
in (let _187_574 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _187_576 _187_575 _187_574))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _187_581 = (let _187_580 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _187_579 = (FStar_Syntax_Print.tag_of_term t0)
in (let _187_578 = (FStar_Syntax_Print.term_to_string t0)
in (let _187_577 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _187_580 _187_579 _187_578 _187_577)))))
in (FStar_All.failwith _187_581))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _187_583 = (let _187_582 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _187_582))
in (FStar_All.failwith _187_583))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _90_678) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _90_683) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _187_584 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((_187_584), ([])))
end
| FStar_Syntax_Syntax.Tm_type (_90_692) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, _90_696) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _187_585 = (encode_const c)
in ((_187_585), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _90_707 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_90_707) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(

let _90_714 = (encode_binders None binders env)
in (match (_90_714) with
| (vars, guards, env', decls, _90_713) -> begin
(

let fsym = (let _187_586 = (varops.fresh "f")
in ((_187_586), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let _90_722 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let _90_718 = env.tcenv
in {FStar_TypeChecker_Env.solver = _90_718.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_718.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_718.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_718.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_718.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_718.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_718.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_718.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_718.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_718.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_718.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_718.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_718.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _90_718.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _90_718.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_718.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_718.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_718.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _90_718.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _90_718.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _90_718.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _90_718.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _90_718.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (_90_722) with
| (pre_opt, res_t) -> begin
(

let _90_725 = (encode_term_pred None res_t env' app)
in (match (_90_725) with
| (res_pred, decls') -> begin
(

let _90_734 = (match (pre_opt) with
| None -> begin
(let _187_587 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_187_587), ([])))
end
| Some (pre) -> begin
(

let _90_731 = (encode_formula pre env')
in (match (_90_731) with
| (guard, decls0) -> begin
(let _187_588 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((_187_588), (decls0)))
end))
end)
in (match (_90_734) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _187_590 = (let _187_589 = (FStar_SMTEncoding_Util.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_187_589)))
in (FStar_SMTEncoding_Util.mkForall _187_590))
in (

let cvars = (let _187_592 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _187_592 (FStar_List.filter (fun _90_739 -> (match (_90_739) with
| (x, _90_738) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (match ((FStar_Util.smap_try_find env.cache tkey_hash)) with
| Some (t', sorts, _90_746) -> begin
(let _187_595 = (let _187_594 = (let _187_593 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t'), (_187_593)))
in (FStar_SMTEncoding_Util.mkApp _187_594))
in ((_187_595), ([])))
end
| None -> begin
(

let tsym = (let _187_597 = (let _187_596 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" _187_596))
in (varops.mk_unique _187_597))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _187_598 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_187_598))
end else begin
None
end
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (let _187_600 = (let _187_599 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (_187_599)))
in (FStar_SMTEncoding_Util.mkApp _187_600))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (let _187_602 = (let _187_601 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_187_601), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_187_602)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _187_609 = (let _187_608 = (let _187_607 = (let _187_606 = (let _187_605 = (let _187_604 = (let _187_603 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _187_603))
in ((f_has_t), (_187_604)))
in (FStar_SMTEncoding_Util.mkImp _187_605))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_187_606)))
in (mkForall_fuel _187_607))
in ((_187_608), (Some ("pre-typing for functions")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_187_609)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (let _187_613 = (let _187_612 = (let _187_611 = (let _187_610 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_187_610)))
in (FStar_SMTEncoding_Util.mkForall _187_611))
in ((_187_612), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_187_613)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp)::[]))))
in (

let _90_765 = (FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))))))
end)))))
end))
end))
end)))))
end))
end else begin
(

let tsym = (varops.fresh "Non_total_Tm_arrow")
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (FStar_SMTEncoding_Util.mkApp ((tsym), ([])))
in (

let t_kinding = (

let a_name = Some ((Prims.strcat "non_total_function_typing_" tsym))
in (let _187_615 = (let _187_614 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((_187_614), (Some ("Typing for non-total arrows")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_187_615)))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _187_622 = (let _187_621 = (let _187_620 = (let _187_619 = (let _187_618 = (let _187_617 = (let _187_616 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _187_616))
in ((f_has_t), (_187_617)))
in (FStar_SMTEncoding_Util.mkImp _187_618))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_187_619)))
in (mkForall_fuel _187_620))
in ((_187_621), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_187_622)))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_90_778) -> begin
(

let _90_798 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _90_785; FStar_Syntax_Syntax.pos = _90_783; FStar_Syntax_Syntax.vars = _90_781} -> begin
(

let _90_793 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_90_793) with
| (b, f) -> begin
(let _187_624 = (let _187_623 = (FStar_List.hd b)
in (Prims.fst _187_623))
in ((_187_624), (f)))
end))
end
| _90_795 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_90_798) with
| (x, f) -> begin
(

let _90_801 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_90_801) with
| (base_t, decls) -> begin
(

let _90_805 = (gen_term_var env x)
in (match (_90_805) with
| (x, xtm, env') -> begin
(

let _90_808 = (encode_formula f env')
in (match (_90_808) with
| (refinement, decls') -> begin
(

let _90_811 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_90_811) with
| (fsym, fterm) -> begin
(

let encoding = (let _187_626 = (let _187_625 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_187_625), (refinement)))
in (FStar_SMTEncoding_Util.mkAnd _187_626))
in (

let cvars = (let _187_628 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _187_628 (FStar_List.filter (fun _90_816 -> (match (_90_816) with
| (y, _90_815) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = ((x), (FStar_SMTEncoding_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_SMTEncoding_Term.Fuel_sort))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((ffv)::(xfv)::cvars), (encoding)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (match ((FStar_Util.smap_try_find env.cache tkey_hash)) with
| Some (t, _90_824, _90_826) -> begin
(let _187_631 = (let _187_630 = (let _187_629 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t), (_187_629)))
in (FStar_SMTEncoding_Util.mkApp _187_630))
in ((_187_631), ([])))
end
| None -> begin
(

let tsym = (let _187_633 = (let _187_632 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_refine_" _187_632))
in (varops.mk_unique _187_633))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (let _187_635 = (let _187_634 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (_187_634)))
in (FStar_SMTEncoding_Util.mkApp _187_635))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t)
in (

let t_haseq = (let _187_639 = (let _187_638 = (let _187_637 = (let _187_636 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (_187_636)))
in (FStar_SMTEncoding_Util.mkForall _187_637))
in ((_187_638), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym)))))
in FStar_SMTEncoding_Term.Assume (_187_639))
in (

let t_kinding = (let _187_641 = (let _187_640 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_187_640), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym)))))
in FStar_SMTEncoding_Term.Assume (_187_641))
in (

let t_interp = (let _187_647 = (let _187_646 = (let _187_643 = (let _187_642 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_187_642)))
in (FStar_SMTEncoding_Util.mkForall _187_643))
in (let _187_645 = (let _187_644 = (FStar_Syntax_Print.term_to_string t0)
in Some (_187_644))
in ((_187_646), (_187_645), (Some ((Prims.strcat "refinement_interpretation_" tsym))))))
in FStar_SMTEncoding_Term.Assume (_187_647))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq)::[])))
in (

let _90_842 = (FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))))))
end)))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(

let ttm = (let _187_648 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar _187_648))
in (

let _90_851 = (encode_term_pred None k env ttm)
in (match (_90_851) with
| (t_has_k, decls) -> begin
(

let d = (let _187_654 = (let _187_653 = (let _187_652 = (let _187_651 = (let _187_650 = (let _187_649 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _187_649))
in (FStar_Util.format1 "uvar_typing_%s" _187_650))
in (varops.mk_unique _187_651))
in Some (_187_652))
in ((t_has_k), (Some ("Uvar typing")), (_187_653)))
in FStar_SMTEncoding_Term.Assume (_187_654))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_90_854) -> begin
(

let _90_858 = (FStar_Syntax_Util.head_and_args t0)
in (match (_90_858) with
| (head, args_e) -> begin
(match ((let _187_656 = (let _187_655 = (FStar_Syntax_Subst.compress head)
in _187_655.FStar_Syntax_Syntax.n)
in ((_187_656), (args_e)))) with
| (_90_860, _90_862) when (head_redex env head) -> begin
(let _187_657 = (whnf env t)
in (encode_term _187_657 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let _90_902 = (encode_term v1 env)
in (match (_90_902) with
| (v1, decls1) -> begin
(

let _90_905 = (encode_term v2 env)
in (match (_90_905) with
| (v2, decls2) -> begin
(let _187_658 = (FStar_SMTEncoding_Util.mk_LexCons v1 v2)
in ((_187_658), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), (_90_914)::(_90_911)::_90_909) -> begin
(

let e0 = (let _187_662 = (let _187_661 = (let _187_660 = (let _187_659 = (FStar_List.hd args_e)
in (_187_659)::[])
in ((head), (_187_660)))
in FStar_Syntax_Syntax.Tm_app (_187_661))
in (FStar_Syntax_Syntax.mk _187_662 None head.FStar_Syntax_Syntax.pos))
in (

let e = (let _187_665 = (let _187_664 = (let _187_663 = (FStar_List.tl args_e)
in ((e0), (_187_663)))
in FStar_Syntax_Syntax.Tm_app (_187_664))
in (FStar_Syntax_Syntax.mk _187_665 None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env)))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), ((arg, _90_923))::[]) -> begin
(

let _90_929 = (encode_term arg env)
in (match (_90_929) with
| (tm, decls) -> begin
(let _187_666 = (FStar_SMTEncoding_Util.mkApp (("Reify"), ((tm)::[])))
in ((_187_666), (decls)))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_90_931)), ((arg, _90_936))::[]) -> begin
(encode_term arg env)
end
| _90_941 -> begin
(

let _90_944 = (encode_args args_e env)
in (match (_90_944) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _90_949 = (encode_term head env)
in (match (_90_949) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let _90_958 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_90_958) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun _90_962 _90_966 -> (match (((_90_962), (_90_966))) with
| ((bv, _90_961), (a, _90_965)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (let _187_671 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _187_671 (FStar_Syntax_Subst.subst subst)))
in (

let _90_971 = (encode_term_pred None ty env app_tm)
in (match (_90_971) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (let _187_678 = (let _187_677 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (let _187_676 = (let _187_675 = (let _187_674 = (let _187_673 = (let _187_672 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string _187_672))
in (Prims.strcat "partial_app_typing_" _187_673))
in (varops.mk_unique _187_674))
in Some (_187_675))
in ((_187_677), (Some ("Partial app typing")), (_187_676))))
in FStar_SMTEncoding_Term.Assume (_187_678))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _90_978 = (lookup_free_var_sym env fv)
in (match (_90_978) with
| (fname, fuel_args) -> begin
(

let tm = (FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args args))))
in ((tm), (decls)))
end)))
in (

let head = (FStar_Syntax_Subst.compress head)
in (

let head_type = (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
Some (x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(let _187_682 = (let _187_681 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _187_681 Prims.snd))
in Some (_187_682))
end
| FStar_Syntax_Syntax.Tm_ascribed (_90_1010, FStar_Util.Inl (t), _90_1014) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_90_1018, FStar_Util.Inr (c), _90_1022) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _90_1026 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (let _187_683 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _187_683))
in (

let _90_1034 = (curried_arrow_formals_comp head_type)
in (match (_90_1034) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _90_1050 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some (((formals), (c)))))
end else begin
(encode_partial_app None)
end
end)
end)))
end)))))
end))
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let _90_1059 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_90_1059) with
| (bs, body, opening) -> begin
(

let fallback = (fun _90_1061 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (let _187_686 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((_187_686), ((decl)::[])))))
end))
in (

let is_impure = (fun _90_10 -> (match (_90_10) with
| FStar_Util.Inl (lc) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)))
end
| FStar_Util.Inr (eff, _90_1069) -> begin
(let _187_689 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right _187_689 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _187_694 = (let _187_692 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _187_692))
in (FStar_All.pipe_right _187_694 (fun _187_693 -> Some (_187_693))))
end
| FStar_Util.Inr (eff, flags) -> begin
(

let new_uvar = (fun _90_1082 -> (match (()) with
| () -> begin
(let _187_697 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _187_697 Prims.fst))
end))
in if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) then begin
(let _187_700 = (let _187_698 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total _187_698))
in (FStar_All.pipe_right _187_700 (fun _187_699 -> Some (_187_699))))
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) then begin
(let _187_703 = (let _187_701 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal _187_701))
in (FStar_All.pipe_right _187_703 (fun _187_702 -> Some (_187_702))))
end else begin
None
end
end)
end))
in (match (lopt) with
| None -> begin
(

let _90_1084 = (let _187_705 = (let _187_704 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _187_704))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _187_705))
in (fallback ()))
end
| Some (lc) -> begin
if (is_impure lc) then begin
(fallback ())
end else begin
(

let _90_1094 = (encode_binders None bs env)
in (match (_90_1094) with
| (vars, guards, envbody, decls, _90_1093) -> begin
(

let _90_1097 = (encode_term body envbody)
in (match (_90_1097) with
| (body, decls') -> begin
(

let key_body = (let _187_709 = (let _187_708 = (let _187_707 = (let _187_706 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_187_706), (body)))
in (FStar_SMTEncoding_Util.mkImp _187_707))
in (([]), (vars), (_187_708)))
in (FStar_SMTEncoding_Util.mkForall _187_709))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (match ((FStar_Util.smap_try_find env.cache tkey_hash)) with
| Some (t, _90_1104, _90_1106) -> begin
(let _187_712 = (let _187_711 = (let _187_710 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((t), (_187_710)))
in (FStar_SMTEncoding_Util.mkApp _187_711))
in ((_187_712), ([])))
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

let fsym = (let _187_714 = (let _187_713 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" _187_713))
in (varops.mk_unique _187_714))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (let _187_716 = (let _187_715 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((fsym), (_187_715)))
in (FStar_SMTEncoding_Util.mkApp _187_716))
in (

let app = (mk_Apply f vars)
in (

let typing_f = (match ((codomain_eff lc)) with
| None -> begin
[]
end
| Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs c)
in (

let _90_1124 = (encode_term_pred None tfun env f)
in (match (_90_1124) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _187_720 = (let _187_719 = (let _187_718 = (let _187_717 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_187_717), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_187_718))
in (_187_719)::[])
in (FStar_List.append decls'' _187_720)))
end)))
end)
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (let _187_724 = (let _187_723 = (let _187_722 = (let _187_721 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_187_721)))
in (FStar_SMTEncoding_Util.mkForall _187_722))
in ((_187_723), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_187_724)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[]))))
in (

let _90_1130 = (FStar_Util.smap_add env.cache tkey_hash ((fsym), (cvar_sorts), (f_decls)))
in ((f), (f_decls)))))))))))
end)
end)))))
end))
end))
end
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_90_1133, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_90_1145); FStar_Syntax_Syntax.lbunivs = _90_1143; FStar_Syntax_Syntax.lbtyp = _90_1141; FStar_Syntax_Syntax.lbeff = _90_1139; FStar_Syntax_Syntax.lbdef = _90_1137})::_90_1135), _90_1151) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _90_1160; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _90_1157; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_90_1170) -> begin
(

let _90_1172 = (FStar_TypeChecker_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (let _187_725 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((_187_725), ((decl_e)::[]))))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let _90_1188 = (encode_term e1 env)
in (match (_90_1188) with
| (ee1, decls1) -> begin
(

let _90_1191 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (_90_1191) with
| (xs, e2) -> begin
(

let _90_1195 = (FStar_List.hd xs)
in (match (_90_1195) with
| (x, _90_1194) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _90_1199 = (encode_body e2 env')
in (match (_90_1199) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let _90_1207 = (encode_term e env)
in (match (_90_1207) with
| (scr, decls) -> begin
(

let _90_1244 = (FStar_List.fold_right (fun b _90_1211 -> (match (_90_1211) with
| (else_case, decls) -> begin
(

let _90_1215 = (FStar_Syntax_Subst.open_branch b)
in (match (_90_1215) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _90_1219 _90_1222 -> (match (((_90_1219), (_90_1222))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _90_1228 -> (match (_90_1228) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let _90_1238 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let _90_1235 = (encode_term w env)
in (match (_90_1235) with
| (w, decls2) -> begin
(let _187_759 = (let _187_758 = (let _187_757 = (let _187_756 = (let _187_755 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w), (_187_755)))
in (FStar_SMTEncoding_Util.mkEq _187_756))
in ((guard), (_187_757)))
in (FStar_SMTEncoding_Util.mkAnd _187_758))
in ((_187_759), (decls2)))
end))
end)
in (match (_90_1238) with
| (guard, decls2) -> begin
(

let _90_1241 = (encode_br br env)
in (match (_90_1241) with
| (br, decls3) -> begin
(let _187_760 = (FStar_SMTEncoding_Util.mkITE ((guard), (br), (else_case)))
in ((_187_760), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (_90_1244) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _90_1250 -> begin
(let _187_763 = (encode_one_pat env pat)
in (_187_763)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _90_1253 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _187_766 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _187_766))
end else begin
()
end
in (

let _90_1257 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_90_1257) with
| (vars, pat_term) -> begin
(

let _90_1269 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _90_1260 v -> (match (_90_1260) with
| (env, vars) -> begin
(

let _90_1266 = (gen_term_var env v)
in (match (_90_1266) with
| (xx, _90_1264, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (_90_1269) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_90_1274) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _187_774 = (let _187_773 = (encode_const c)
in ((scrutinee), (_187_773)))
in (FStar_SMTEncoding_Util.mkEq _187_774))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _90_1296 -> (match (_90_1296) with
| (arg, _90_1295) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _187_777 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _187_777)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_90_1303) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_90_1313) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _187_785 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _90_1323 -> (match (_90_1323) with
| (arg, _90_1322) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _187_784 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _187_784)))
end))))
in (FStar_All.pipe_right _187_785 FStar_List.flatten))
end))
in (

let pat_term = (fun _90_1326 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let _90_1342 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _90_1332 _90_1336 -> (match (((_90_1332), (_90_1336))) with
| ((tms, decls), (t, _90_1335)) -> begin
(

let _90_1339 = (encode_term t env)
in (match (_90_1339) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (_90_1342) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let list_elements = (fun e -> (match ((FStar_Syntax_Util.list_elements e)) with
| Some (l) -> begin
l
end
| None -> begin
(

let _90_1352 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (

let one_pat = (fun p -> (

let _90_1358 = (let _187_800 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _187_800 FStar_Syntax_Util.head_and_args))
in (match (_90_1358) with
| (head, args) -> begin
(match ((let _187_802 = (let _187_801 = (FStar_Syntax_Util.un_uinst head)
in _187_801.FStar_Syntax_Syntax.n)
in ((_187_802), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((_90_1366, _90_1368))::((e, _90_1363))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _90_1376))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| _90_1381 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let _90_1389 = (let _187_807 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _187_807 FStar_Syntax_Util.head_and_args))
in (match (_90_1389) with
| (head, args) -> begin
(match ((let _187_809 = (let _187_808 = (FStar_Syntax_Util.un_uinst head)
in _187_808.FStar_Syntax_Syntax.n)
in ((_187_809), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _90_1394))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _90_1399 -> begin
None
end)
end)))
in (match (elts) with
| (t)::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _187_812 = (list_elements e)
in (FStar_All.pipe_right _187_812 (FStar_List.map (fun branch -> (let _187_811 = (list_elements branch)
in (FStar_All.pipe_right _187_811 (FStar_List.map one_pat)))))))
end
| _90_1406 -> begin
(let _187_813 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_187_813)::[])
end)
end
| _90_1408 -> begin
(let _187_814 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_187_814)::[])
end))))
in (

let _90_1451 = (match ((let _187_815 = (FStar_Syntax_Subst.compress t)
in _187_815.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _90_1415 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_90_1415) with
| (binders, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = _90_1436; FStar_Syntax_Syntax.effect_name = _90_1434; FStar_Syntax_Syntax.result_typ = _90_1432; FStar_Syntax_Syntax.effect_args = ((pre, _90_1428))::((post, _90_1424))::((pats, _90_1420))::[]; FStar_Syntax_Syntax.flags = _90_1417}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _187_816 = (lemma_pats pats')
in ((binders), (pre), (post), (_187_816))))
end
| _90_1444 -> begin
(FStar_All.failwith "impos")
end)
end))
end
| _90_1446 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_90_1451) with
| (binders, pre, post, patterns) -> begin
(

let _90_1458 = (encode_binders None binders env)
in (match (_90_1458) with
| (vars, guards, env, decls, _90_1457) -> begin
(

let _90_1471 = (let _187_820 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _90_1468 = (let _187_819 = (FStar_All.pipe_right branch (FStar_List.map (fun _90_1463 -> (match (_90_1463) with
| (t, _90_1462) -> begin
(encode_term t (

let _90_1464 = env
in {bindings = _90_1464.bindings; depth = _90_1464.depth; tcenv = _90_1464.tcenv; warn = _90_1464.warn; cache = _90_1464.cache; nolabels = _90_1464.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _90_1464.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _187_819 FStar_List.unzip))
in (match (_90_1468) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _187_820 FStar_List.unzip))
in (match (_90_1471) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _187_823 = (let _187_822 = (FStar_SMTEncoding_Util.mkFreeV l)
in (FStar_SMTEncoding_Util.mk_Precedes _187_822 e))
in (_187_823)::p))))
end
| _90_1481 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _187_829 = (FStar_SMTEncoding_Util.mk_Precedes tl e)
in (_187_829)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _187_831 = (let _187_830 = (FStar_SMTEncoding_Util.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mk_LexCons _187_830 tl))
in (aux _187_831 vars))
end
| _90_1493 -> begin
pats
end))
in (let _187_832 = (FStar_SMTEncoding_Util.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux _187_832 vars)))
end)
end)
in (

let env = (

let _90_1495 = env
in {bindings = _90_1495.bindings; depth = _90_1495.depth; tcenv = _90_1495.tcenv; warn = _90_1495.warn; cache = _90_1495.cache; nolabels = true; use_zfuel_name = _90_1495.use_zfuel_name; encode_non_total_function_typ = _90_1495.encode_non_total_function_typ})
in (

let _90_1500 = (let _187_833 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _187_833 env))
in (match (_90_1500) with
| (pre, decls'') -> begin
(

let _90_1503 = (let _187_834 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _187_834 env))
in (match (_90_1503) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (let _187_839 = (let _187_838 = (let _187_837 = (let _187_836 = (let _187_835 = (FStar_SMTEncoding_Util.mk_and_l ((pre)::guards))
in ((_187_835), (post)))
in (FStar_SMTEncoding_Util.mkImp _187_836))
in ((pats), (vars), (_187_837)))
in (FStar_SMTEncoding_Util.mkForall _187_838))
in ((_187_839), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _187_845 = (FStar_Syntax_Print.tag_of_term phi)
in (let _187_844 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _187_845 _187_844)))
end else begin
()
end)
in (

let enc = (fun f r l -> (

let _90_1520 = (FStar_Util.fold_map (fun decls x -> (

let _90_1517 = (encode_term (Prims.fst x) env)
in (match (_90_1517) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (_90_1520) with
| (decls, args) -> begin
(let _187_867 = (

let _90_1521 = (f args)
in {FStar_SMTEncoding_Term.tm = _90_1521.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = _90_1521.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((_187_867), (decls)))
end)))
in (

let const_op = (fun f r _90_1526 -> (let _187_879 = (f r)
in ((_187_879), ([]))))
in (

let un_op = (fun f l -> (let _187_889 = (FStar_List.hd l)
in (FStar_All.pipe_left f _187_889)))
in (

let bin_op = (fun f _90_11 -> (match (_90_11) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| _90_1537 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let _90_1553 = (FStar_Util.fold_map (fun decls _90_1547 -> (match (_90_1547) with
| (t, _90_1546) -> begin
(

let _90_1550 = (encode_formula t env)
in (match (_90_1550) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (_90_1553) with
| (decls, phis) -> begin
(let _187_920 = (

let _90_1554 = (f phis)
in {FStar_SMTEncoding_Term.tm = _90_1554.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = _90_1554.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((_187_920), (decls)))
end)))
in (

let eq_op = (fun r _90_12 -> (match (_90_12) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(enc (bin_op FStar_SMTEncoding_Util.mkEq) r ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Util.mkEq) r l)
end))
in (

let mk_imp = (fun r _90_13 -> (match (_90_13) with
| ((lhs, _90_1579))::((rhs, _90_1575))::[] -> begin
(

let _90_1584 = (encode_formula rhs env)
in (match (_90_1584) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _90_1587) -> begin
((l1), (decls1))
end
| _90_1591 -> begin
(

let _90_1594 = (encode_formula lhs env)
in (match (_90_1594) with
| (l2, decls2) -> begin
(let _187_937 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((_187_937), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| _90_1596 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun r _90_14 -> (match (_90_14) with
| ((guard, _90_1610))::((_then, _90_1606))::((_else, _90_1602))::[] -> begin
(

let _90_1615 = (encode_formula guard env)
in (match (_90_1615) with
| (g, decls1) -> begin
(

let _90_1618 = (encode_formula _then env)
in (match (_90_1618) with
| (t, decls2) -> begin
(

let _90_1621 = (encode_formula _else env)
in (match (_90_1621) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| _90_1624 -> begin
(FStar_All.failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _187_955 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _187_955)))
in (

let connectives = (let _187_1058 = (let _187_971 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Syntax_Const.and_lid), (_187_971)))
in (let _187_1057 = (let _187_1056 = (let _187_981 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Syntax_Const.or_lid), (_187_981)))
in (let _187_1055 = (let _187_1054 = (let _187_1053 = (let _187_999 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Syntax_Const.iff_lid), (_187_999)))
in (let _187_1052 = (let _187_1051 = (let _187_1050 = (let _187_1017 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Syntax_Const.not_lid), (_187_1017)))
in (_187_1050)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::_187_1051)
in (_187_1053)::_187_1052))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::_187_1054)
in (_187_1056)::_187_1055))
in (_187_1058)::_187_1057))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let _90_1641 = (encode_formula phi' env)
in (match (_90_1641) with
| (phi, decls) -> begin
(let _187_1061 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))) r)
in ((_187_1061), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (_90_1643) -> begin
(let _187_1062 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula _187_1062 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let _90_1651 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (_90_1651) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _90_1658; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _90_1655; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _90_1669 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_90_1669) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_90_1686)::((x, _90_1683))::((t, _90_1679))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let _90_1691 = (encode_term x env)
in (match (_90_1691) with
| (x, decls) -> begin
(

let _90_1694 = (encode_term t env)
in (match (_90_1694) with
| (t, decls') -> begin
(let _187_1063 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((_187_1063), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, _90_1707))::((msg, _90_1703))::((phi, _90_1699))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _187_1067 = (let _187_1064 = (FStar_Syntax_Subst.compress r)
in _187_1064.FStar_Syntax_Syntax.n)
in (let _187_1066 = (let _187_1065 = (FStar_Syntax_Subst.compress msg)
in _187_1065.FStar_Syntax_Syntax.n)
in ((_187_1067), (_187_1066))))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _90_1716))) -> begin
(

let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false))))))) None r)
in (fallback phi))
end
| _90_1723 -> begin
(fallback phi)
end)
end
| _90_1725 when (head_redex env head) -> begin
(let _187_1068 = (whnf env phi)
in (encode_formula _187_1068 env))
end
| _90_1727 -> begin
(

let _90_1730 = (encode_term phi env)
in (match (_90_1730) with
| (tt, decls) -> begin
(let _187_1069 = (FStar_SMTEncoding_Term.mk_Valid (

let _90_1731 = tt
in {FStar_SMTEncoding_Term.tm = _90_1731.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = _90_1731.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((_187_1069), (decls)))
end))
end))
end
| _90_1734 -> begin
(

let _90_1737 = (encode_term phi env)
in (match (_90_1737) with
| (tt, decls) -> begin
(let _187_1070 = (FStar_SMTEncoding_Term.mk_Valid (

let _90_1738 = tt
in {FStar_SMTEncoding_Term.tm = _90_1738.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = _90_1738.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((_187_1070), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _90_1751 = (encode_binders None bs env)
in (match (_90_1751) with
| (vars, guards, env, decls, _90_1750) -> begin
(

let _90_1764 = (let _187_1082 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _90_1761 = (let _187_1081 = (FStar_All.pipe_right p (FStar_List.map (fun _90_1756 -> (match (_90_1756) with
| (t, _90_1755) -> begin
(encode_term t (

let _90_1757 = env
in {bindings = _90_1757.bindings; depth = _90_1757.depth; tcenv = _90_1757.tcenv; warn = _90_1757.warn; cache = _90_1757.cache; nolabels = _90_1757.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _90_1757.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _187_1081 FStar_List.unzip))
in (match (_90_1761) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _187_1082 FStar_List.unzip))
in (match (_90_1764) with
| (pats, decls') -> begin
(

let _90_1767 = (encode_formula body env)
in (match (_90_1767) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = _90_1771; FStar_SMTEncoding_Term.rng = _90_1769})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| _90_1782 -> begin
guards
end)
in (let _187_1083 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((vars), (pats), (_187_1083), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in (

let _90_1784 = (debug phi)
in (

let phi = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun _90_1793 -> (match (_90_1793) with
| (x, _90_1792) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats) with
| [] -> begin
()
end
| (hd)::tl -> begin
(

let pat_vars = (let _187_1092 = (FStar_Syntax_Free.names hd)
in (FStar_List.fold_left (fun out x -> (let _187_1091 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out _187_1091))) _187_1092 tl))
in (match ((FStar_All.pipe_right vars (FStar_Util.find_opt (fun _90_1805 -> (match (_90_1805) with
| (b, _90_1804) -> begin
(not ((FStar_Util.set_mem b pat_vars)))
end))))) with
| None -> begin
()
end
| Some (x, _90_1809) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd.FStar_Syntax_Syntax.pos tl)
in (let _187_1097 = (let _187_1096 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Pattern misses at least one bound variable: %s" _187_1096))
in (FStar_TypeChecker_Errors.warn pos _187_1097)))
end))
end)))
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _90_1824 -> (match (_90_1824) with
| (l, _90_1823) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_90_1827, f) -> begin
(f phi.FStar_Syntax_Syntax.pos arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(

let _90_1837 = (FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)))
in (

let _90_1844 = (encode_q_body env vars pats body)
in (match (_90_1844) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _187_1130 = (let _187_1129 = (FStar_SMTEncoding_Util.mkImp ((guard), (body)))
in ((pats), (vars), (_187_1129)))
in (FStar_SMTEncoding_Term.mkForall _187_1130 phi.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(

let _90_1852 = (FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)))
in (

let _90_1859 = (encode_q_body env vars pats body)
in (match (_90_1859) with
| (vars, pats, guard, body, decls) -> begin
(let _187_1133 = (let _187_1132 = (let _187_1131 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body)))
in ((pats), (vars), (_187_1131)))
in (FStar_SMTEncoding_Term.mkExists _187_1132 phi.FStar_Syntax_Syntax.pos))
in ((_187_1133), (decls)))
end)))
end))))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _90_1865 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_90_1865) with
| (asym, a) -> begin
(

let _90_1868 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_90_1868) with
| (xsym, x) -> begin
(

let _90_1871 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_90_1871) with
| (ysym, y) -> begin
(

let quant = (fun vars body x -> (

let xname_decl = (let _187_1170 = (let _187_1169 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_187_1169), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_187_1170))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (let _187_1172 = (let _187_1171 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x), (_187_1171)))
in (FStar_SMTEncoding_Util.mkApp _187_1172))
in (

let xtok = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (let _187_1186 = (let _187_1185 = (let _187_1184 = (let _187_1183 = (let _187_1176 = (let _187_1175 = (let _187_1174 = (let _187_1173 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (_187_1173)))
in (FStar_SMTEncoding_Util.mkForall _187_1174))
in ((_187_1175), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (_187_1176))
in (let _187_1182 = (let _187_1181 = (let _187_1180 = (let _187_1179 = (let _187_1178 = (let _187_1177 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (_187_1177)))
in (FStar_SMTEncoding_Util.mkForall _187_1178))
in ((_187_1179), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x)))))
in FStar_SMTEncoding_Term.Assume (_187_1180))
in (_187_1181)::[])
in (_187_1183)::_187_1182))
in (xtok_decl)::_187_1184)
in (xname_decl)::_187_1185)
in ((xtok), (_187_1186))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (let _187_1346 = (let _187_1195 = (let _187_1194 = (let _187_1193 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1193))
in (quant axy _187_1194))
in ((FStar_Syntax_Const.op_Eq), (_187_1195)))
in (let _187_1345 = (let _187_1344 = (let _187_1202 = (let _187_1201 = (let _187_1200 = (let _187_1199 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot _187_1199))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1200))
in (quant axy _187_1201))
in ((FStar_Syntax_Const.op_notEq), (_187_1202)))
in (let _187_1343 = (let _187_1342 = (let _187_1211 = (let _187_1210 = (let _187_1209 = (let _187_1208 = (let _187_1207 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1206 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1207), (_187_1206))))
in (FStar_SMTEncoding_Util.mkLT _187_1208))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1209))
in (quant xy _187_1210))
in ((FStar_Syntax_Const.op_LT), (_187_1211)))
in (let _187_1341 = (let _187_1340 = (let _187_1220 = (let _187_1219 = (let _187_1218 = (let _187_1217 = (let _187_1216 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1215 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1216), (_187_1215))))
in (FStar_SMTEncoding_Util.mkLTE _187_1217))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1218))
in (quant xy _187_1219))
in ((FStar_Syntax_Const.op_LTE), (_187_1220)))
in (let _187_1339 = (let _187_1338 = (let _187_1229 = (let _187_1228 = (let _187_1227 = (let _187_1226 = (let _187_1225 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1224 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1225), (_187_1224))))
in (FStar_SMTEncoding_Util.mkGT _187_1226))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1227))
in (quant xy _187_1228))
in ((FStar_Syntax_Const.op_GT), (_187_1229)))
in (let _187_1337 = (let _187_1336 = (let _187_1238 = (let _187_1237 = (let _187_1236 = (let _187_1235 = (let _187_1234 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1233 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1234), (_187_1233))))
in (FStar_SMTEncoding_Util.mkGTE _187_1235))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1236))
in (quant xy _187_1237))
in ((FStar_Syntax_Const.op_GTE), (_187_1238)))
in (let _187_1335 = (let _187_1334 = (let _187_1247 = (let _187_1246 = (let _187_1245 = (let _187_1244 = (let _187_1243 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1242 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1243), (_187_1242))))
in (FStar_SMTEncoding_Util.mkSub _187_1244))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _187_1245))
in (quant xy _187_1246))
in ((FStar_Syntax_Const.op_Subtraction), (_187_1247)))
in (let _187_1333 = (let _187_1332 = (let _187_1254 = (let _187_1253 = (let _187_1252 = (let _187_1251 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus _187_1251))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _187_1252))
in (quant qx _187_1253))
in ((FStar_Syntax_Const.op_Minus), (_187_1254)))
in (let _187_1331 = (let _187_1330 = (let _187_1263 = (let _187_1262 = (let _187_1261 = (let _187_1260 = (let _187_1259 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1258 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1259), (_187_1258))))
in (FStar_SMTEncoding_Util.mkAdd _187_1260))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _187_1261))
in (quant xy _187_1262))
in ((FStar_Syntax_Const.op_Addition), (_187_1263)))
in (let _187_1329 = (let _187_1328 = (let _187_1272 = (let _187_1271 = (let _187_1270 = (let _187_1269 = (let _187_1268 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1267 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1268), (_187_1267))))
in (FStar_SMTEncoding_Util.mkMul _187_1269))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _187_1270))
in (quant xy _187_1271))
in ((FStar_Syntax_Const.op_Multiply), (_187_1272)))
in (let _187_1327 = (let _187_1326 = (let _187_1281 = (let _187_1280 = (let _187_1279 = (let _187_1278 = (let _187_1277 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1276 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1277), (_187_1276))))
in (FStar_SMTEncoding_Util.mkDiv _187_1278))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _187_1279))
in (quant xy _187_1280))
in ((FStar_Syntax_Const.op_Division), (_187_1281)))
in (let _187_1325 = (let _187_1324 = (let _187_1290 = (let _187_1289 = (let _187_1288 = (let _187_1287 = (let _187_1286 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1285 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_187_1286), (_187_1285))))
in (FStar_SMTEncoding_Util.mkMod _187_1287))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _187_1288))
in (quant xy _187_1289))
in ((FStar_Syntax_Const.op_Modulus), (_187_1290)))
in (let _187_1323 = (let _187_1322 = (let _187_1299 = (let _187_1298 = (let _187_1297 = (let _187_1296 = (let _187_1295 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _187_1294 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_187_1295), (_187_1294))))
in (FStar_SMTEncoding_Util.mkAnd _187_1296))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1297))
in (quant xy _187_1298))
in ((FStar_Syntax_Const.op_And), (_187_1299)))
in (let _187_1321 = (let _187_1320 = (let _187_1308 = (let _187_1307 = (let _187_1306 = (let _187_1305 = (let _187_1304 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _187_1303 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_187_1304), (_187_1303))))
in (FStar_SMTEncoding_Util.mkOr _187_1305))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1306))
in (quant xy _187_1307))
in ((FStar_Syntax_Const.op_Or), (_187_1308)))
in (let _187_1319 = (let _187_1318 = (let _187_1315 = (let _187_1314 = (let _187_1313 = (let _187_1312 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot _187_1312))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1313))
in (quant qx _187_1314))
in ((FStar_Syntax_Const.op_Negation), (_187_1315)))
in (_187_1318)::[])
in (_187_1320)::_187_1319))
in (_187_1322)::_187_1321))
in (_187_1324)::_187_1323))
in (_187_1326)::_187_1325))
in (_187_1328)::_187_1327))
in (_187_1330)::_187_1329))
in (_187_1332)::_187_1331))
in (_187_1334)::_187_1333))
in (_187_1336)::_187_1335))
in (_187_1338)::_187_1337))
in (_187_1340)::_187_1339))
in (_187_1342)::_187_1341))
in (_187_1344)::_187_1343))
in (_187_1346)::_187_1345))
in (

let mk = (fun l v -> (let _187_1393 = (let _187_1392 = (FStar_All.pipe_right prims (FStar_List.find (fun _90_1891 -> (match (_90_1891) with
| (l', _90_1890) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _187_1392 (FStar_Option.map (fun _90_1895 -> (match (_90_1895) with
| (_90_1893, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right _187_1393 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _90_1901 -> (match (_90_1901) with
| (l', _90_1900) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let _90_1907 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_90_1907) with
| (xxsym, xx) -> begin
(

let _90_1910 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_90_1910) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (let _187_1423 = (let _187_1422 = (let _187_1417 = (let _187_1416 = (let _187_1415 = (let _187_1414 = (let _187_1413 = (let _187_1412 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_187_1412)))
in (FStar_SMTEncoding_Util.mkEq _187_1413))
in ((xx_has_type), (_187_1414)))
in (FStar_SMTEncoding_Util.mkImp _187_1415))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (_187_1416)))
in (FStar_SMTEncoding_Util.mkForall _187_1417))
in (let _187_1421 = (let _187_1420 = (let _187_1419 = (let _187_1418 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "pretyping_" _187_1418))
in (varops.mk_unique _187_1419))
in Some (_187_1420))
in ((_187_1422), (Some ("pretyping")), (_187_1421))))
in FStar_SMTEncoding_Term.Assume (_187_1423))))
end))
end)))


let primitive_type_axioms : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV yy)
in (

let mk_unit = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _187_1444 = (let _187_1435 = (let _187_1434 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((_187_1434), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (_187_1435))
in (let _187_1443 = (let _187_1442 = (let _187_1441 = (let _187_1440 = (let _187_1439 = (let _187_1438 = (let _187_1437 = (let _187_1436 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (_187_1436)))
in (FStar_SMTEncoding_Util.mkImp _187_1437))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_187_1438)))
in (mkForall_fuel _187_1439))
in ((_187_1440), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (_187_1441))
in (_187_1442)::[])
in (_187_1444)::_187_1443))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (let _187_1467 = (let _187_1458 = (let _187_1457 = (let _187_1456 = (let _187_1455 = (let _187_1452 = (let _187_1451 = (FStar_SMTEncoding_Term.boxBool b)
in (_187_1451)::[])
in (_187_1452)::[])
in (let _187_1454 = (let _187_1453 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _187_1453 tt))
in ((_187_1455), ((bb)::[]), (_187_1454))))
in (FStar_SMTEncoding_Util.mkForall _187_1456))
in ((_187_1457), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (_187_1458))
in (let _187_1466 = (let _187_1465 = (let _187_1464 = (let _187_1463 = (let _187_1462 = (let _187_1461 = (let _187_1460 = (let _187_1459 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_187_1459)))
in (FStar_SMTEncoding_Util.mkImp _187_1460))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_187_1461)))
in (mkForall_fuel _187_1462))
in ((_187_1463), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (_187_1464))
in (_187_1465)::[])
in (_187_1467)::_187_1466))))))
in (

let mk_int = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Int_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Int_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let precedes = (let _187_1481 = (let _187_1480 = (let _187_1479 = (let _187_1478 = (let _187_1477 = (let _187_1476 = (FStar_SMTEncoding_Term.boxInt a)
in (let _187_1475 = (let _187_1474 = (FStar_SMTEncoding_Term.boxInt b)
in (_187_1474)::[])
in (_187_1476)::_187_1475))
in (tt)::_187_1477)
in (tt)::_187_1478)
in (("Prims.Precedes"), (_187_1479)))
in (FStar_SMTEncoding_Util.mkApp _187_1480))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _187_1481))
in (

let precedes_y_x = (let _187_1482 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _187_1482))
in (let _187_1524 = (let _187_1490 = (let _187_1489 = (let _187_1488 = (let _187_1487 = (let _187_1484 = (let _187_1483 = (FStar_SMTEncoding_Term.boxInt b)
in (_187_1483)::[])
in (_187_1484)::[])
in (let _187_1486 = (let _187_1485 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _187_1485 tt))
in ((_187_1487), ((bb)::[]), (_187_1486))))
in (FStar_SMTEncoding_Util.mkForall _187_1488))
in ((_187_1489), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (_187_1490))
in (let _187_1523 = (let _187_1522 = (let _187_1496 = (let _187_1495 = (let _187_1494 = (let _187_1493 = (let _187_1492 = (let _187_1491 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_187_1491)))
in (FStar_SMTEncoding_Util.mkImp _187_1492))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_187_1493)))
in (mkForall_fuel _187_1494))
in ((_187_1495), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (_187_1496))
in (let _187_1521 = (let _187_1520 = (let _187_1519 = (let _187_1518 = (let _187_1517 = (let _187_1516 = (let _187_1515 = (let _187_1514 = (let _187_1513 = (let _187_1512 = (let _187_1511 = (let _187_1510 = (let _187_1499 = (let _187_1498 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _187_1497 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((_187_1498), (_187_1497))))
in (FStar_SMTEncoding_Util.mkGT _187_1499))
in (let _187_1509 = (let _187_1508 = (let _187_1502 = (let _187_1501 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _187_1500 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((_187_1501), (_187_1500))))
in (FStar_SMTEncoding_Util.mkGTE _187_1502))
in (let _187_1507 = (let _187_1506 = (let _187_1505 = (let _187_1504 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _187_1503 = (FStar_SMTEncoding_Term.unboxInt x)
in ((_187_1504), (_187_1503))))
in (FStar_SMTEncoding_Util.mkLT _187_1505))
in (_187_1506)::[])
in (_187_1508)::_187_1507))
in (_187_1510)::_187_1509))
in (typing_pred_y)::_187_1511)
in (typing_pred)::_187_1512)
in (FStar_SMTEncoding_Util.mk_and_l _187_1513))
in ((_187_1514), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp _187_1515))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_187_1516)))
in (mkForall_fuel _187_1517))
in ((_187_1518), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (_187_1519))
in (_187_1520)::[])
in (_187_1522)::_187_1521))
in (_187_1524)::_187_1523)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (let _187_1547 = (let _187_1538 = (let _187_1537 = (let _187_1536 = (let _187_1535 = (let _187_1532 = (let _187_1531 = (FStar_SMTEncoding_Term.boxString b)
in (_187_1531)::[])
in (_187_1532)::[])
in (let _187_1534 = (let _187_1533 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _187_1533 tt))
in ((_187_1535), ((bb)::[]), (_187_1534))))
in (FStar_SMTEncoding_Util.mkForall _187_1536))
in ((_187_1537), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (_187_1538))
in (let _187_1546 = (let _187_1545 = (let _187_1544 = (let _187_1543 = (let _187_1542 = (let _187_1541 = (let _187_1540 = (let _187_1539 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (_187_1539)))
in (FStar_SMTEncoding_Util.mkImp _187_1540))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_187_1541)))
in (mkForall_fuel _187_1542))
in ((_187_1543), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (_187_1544))
in (_187_1545)::[])
in (_187_1547)::_187_1546))))))
in (

let mk_ref = (fun env reft_name _90_1950 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (let _187_1556 = (let _187_1555 = (let _187_1554 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (_187_1554)::[])
in ((reft_name), (_187_1555)))
in (FStar_SMTEncoding_Util.mkApp _187_1556))
in (

let refb = (let _187_1559 = (let _187_1558 = (let _187_1557 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (_187_1557)::[])
in ((reft_name), (_187_1558)))
in (FStar_SMTEncoding_Util.mkApp _187_1559))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _187_1578 = (let _187_1565 = (let _187_1564 = (let _187_1563 = (let _187_1562 = (let _187_1561 = (let _187_1560 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_187_1560)))
in (FStar_SMTEncoding_Util.mkImp _187_1561))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_187_1562)))
in (mkForall_fuel _187_1563))
in ((_187_1564), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (_187_1565))
in (let _187_1577 = (let _187_1576 = (let _187_1575 = (let _187_1574 = (let _187_1573 = (let _187_1572 = (let _187_1571 = (let _187_1570 = (FStar_SMTEncoding_Util.mkAnd ((typing_pred), (typing_pred_b)))
in (let _187_1569 = (let _187_1568 = (let _187_1567 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (let _187_1566 = (FStar_SMTEncoding_Util.mkFreeV bb)
in ((_187_1567), (_187_1566))))
in (FStar_SMTEncoding_Util.mkEq _187_1568))
in ((_187_1570), (_187_1569))))
in (FStar_SMTEncoding_Util.mkImp _187_1571))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_187_1572)))
in (mkForall_fuel' (Prims.parse_int "2") _187_1573))
in ((_187_1574), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (_187_1575))
in (_187_1576)::[])
in (_187_1578)::_187_1577))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), (Some ("true_interp")))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (let _187_1593 = (let _187_1592 = (let _187_1591 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((_187_1591), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1592))
in (_187_1593)::[])))
in (

let mk_and_interp = (fun env conj _90_1972 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (let _187_1602 = (let _187_1601 = (let _187_1600 = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (_187_1600)::[])
in (("Valid"), (_187_1601)))
in (FStar_SMTEncoding_Util.mkApp _187_1602))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _187_1609 = (let _187_1608 = (let _187_1607 = (let _187_1606 = (let _187_1605 = (let _187_1604 = (let _187_1603 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((_187_1603), (valid)))
in (FStar_SMTEncoding_Util.mkIff _187_1604))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_187_1605)))
in (FStar_SMTEncoding_Util.mkForall _187_1606))
in ((_187_1607), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1608))
in (_187_1609)::[])))))))))
in (

let mk_or_interp = (fun env disj _90_1984 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (let _187_1618 = (let _187_1617 = (let _187_1616 = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (_187_1616)::[])
in (("Valid"), (_187_1617)))
in (FStar_SMTEncoding_Util.mkApp _187_1618))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _187_1625 = (let _187_1624 = (let _187_1623 = (let _187_1622 = (let _187_1621 = (let _187_1620 = (let _187_1619 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((_187_1619), (valid)))
in (FStar_SMTEncoding_Util.mkIff _187_1620))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_187_1621)))
in (FStar_SMTEncoding_Util.mkForall _187_1622))
in ((_187_1623), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1624))
in (_187_1625)::[])))))))))
in (

let mk_eq2_interp = (fun env eq2 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let y = (FStar_SMTEncoding_Util.mkFreeV yy)
in (

let valid = (let _187_1634 = (let _187_1633 = (let _187_1632 = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (_187_1632)::[])
in (("Valid"), (_187_1633)))
in (FStar_SMTEncoding_Util.mkApp _187_1634))
in (let _187_1641 = (let _187_1640 = (let _187_1639 = (let _187_1638 = (let _187_1637 = (let _187_1636 = (let _187_1635 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((_187_1635), (valid)))
in (FStar_SMTEncoding_Util.mkIff _187_1636))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (_187_1637)))
in (FStar_SMTEncoding_Util.mkForall _187_1638))
in ((_187_1639), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1640))
in (_187_1641)::[])))))))))
in (

let mk_eq3_interp = (fun env eq3 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let y = (FStar_SMTEncoding_Util.mkFreeV yy)
in (

let valid = (let _187_1650 = (let _187_1649 = (let _187_1648 = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (_187_1648)::[])
in (("Valid"), (_187_1649)))
in (FStar_SMTEncoding_Util.mkApp _187_1650))
in (let _187_1657 = (let _187_1656 = (let _187_1655 = (let _187_1654 = (let _187_1653 = (let _187_1652 = (let _187_1651 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((_187_1651), (valid)))
in (FStar_SMTEncoding_Util.mkIff _187_1652))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_187_1653)))
in (FStar_SMTEncoding_Util.mkForall _187_1654))
in ((_187_1655), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1656))
in (_187_1657)::[])))))))))))
in (

let mk_imp_interp = (fun env imp tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (let _187_1666 = (let _187_1665 = (let _187_1664 = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (_187_1664)::[])
in (("Valid"), (_187_1665)))
in (FStar_SMTEncoding_Util.mkApp _187_1666))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _187_1673 = (let _187_1672 = (let _187_1671 = (let _187_1670 = (let _187_1669 = (let _187_1668 = (let _187_1667 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((_187_1667), (valid)))
in (FStar_SMTEncoding_Util.mkIff _187_1668))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_187_1669)))
in (FStar_SMTEncoding_Util.mkForall _187_1670))
in ((_187_1671), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1672))
in (_187_1673)::[])))))))))
in (

let mk_iff_interp = (fun env iff tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (let _187_1682 = (let _187_1681 = (let _187_1680 = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (_187_1680)::[])
in (("Valid"), (_187_1681)))
in (FStar_SMTEncoding_Util.mkApp _187_1682))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (let _187_1689 = (let _187_1688 = (let _187_1687 = (let _187_1686 = (let _187_1685 = (let _187_1684 = (let _187_1683 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((_187_1683), (valid)))
in (FStar_SMTEncoding_Util.mkIff _187_1684))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_187_1685)))
in (FStar_SMTEncoding_Util.mkForall _187_1686))
in ((_187_1687), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1688))
in (_187_1689)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let valid = (let _187_1698 = (let _187_1697 = (let _187_1696 = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (_187_1696)::[])
in (("Valid"), (_187_1697)))
in (FStar_SMTEncoding_Util.mkApp _187_1698))
in (

let not_valid_a = (let _187_1699 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot _187_1699))
in (let _187_1704 = (let _187_1703 = (let _187_1702 = (let _187_1701 = (let _187_1700 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (_187_1700)))
in (FStar_SMTEncoding_Util.mkForall _187_1701))
in ((_187_1702), (Some ("not interpretation")), (Some ("l_not-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1703))
in (_187_1704)::[]))))))
in (

let mk_forall_interp = (fun env for_all tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid = (let _187_1713 = (let _187_1712 = (let _187_1711 = (FStar_SMTEncoding_Util.mkApp ((for_all), ((a)::(b)::[])))
in (_187_1711)::[])
in (("Valid"), (_187_1712)))
in (FStar_SMTEncoding_Util.mkApp _187_1713))
in (

let valid_b_x = (let _187_1716 = (let _187_1715 = (let _187_1714 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (_187_1714)::[])
in (("Valid"), (_187_1715)))
in (FStar_SMTEncoding_Util.mkApp _187_1716))
in (let _187_1730 = (let _187_1729 = (let _187_1728 = (let _187_1727 = (let _187_1726 = (let _187_1725 = (let _187_1724 = (let _187_1723 = (let _187_1722 = (let _187_1718 = (let _187_1717 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_187_1717)::[])
in (_187_1718)::[])
in (let _187_1721 = (let _187_1720 = (let _187_1719 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_187_1719), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp _187_1720))
in ((_187_1722), ((xx)::[]), (_187_1721))))
in (FStar_SMTEncoding_Util.mkForall _187_1723))
in ((_187_1724), (valid)))
in (FStar_SMTEncoding_Util.mkIff _187_1725))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_187_1726)))
in (FStar_SMTEncoding_Util.mkForall _187_1727))
in ((_187_1728), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1729))
in (_187_1730)::[]))))))))))
in (

let mk_exists_interp = (fun env for_some tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid = (let _187_1739 = (let _187_1738 = (let _187_1737 = (FStar_SMTEncoding_Util.mkApp ((for_some), ((a)::(b)::[])))
in (_187_1737)::[])
in (("Valid"), (_187_1738)))
in (FStar_SMTEncoding_Util.mkApp _187_1739))
in (

let valid_b_x = (let _187_1742 = (let _187_1741 = (let _187_1740 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (_187_1740)::[])
in (("Valid"), (_187_1741)))
in (FStar_SMTEncoding_Util.mkApp _187_1742))
in (let _187_1756 = (let _187_1755 = (let _187_1754 = (let _187_1753 = (let _187_1752 = (let _187_1751 = (let _187_1750 = (let _187_1749 = (let _187_1748 = (let _187_1744 = (let _187_1743 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_187_1743)::[])
in (_187_1744)::[])
in (let _187_1747 = (let _187_1746 = (let _187_1745 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_187_1745), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp _187_1746))
in ((_187_1748), ((xx)::[]), (_187_1747))))
in (FStar_SMTEncoding_Util.mkExists _187_1749))
in ((_187_1750), (valid)))
in (FStar_SMTEncoding_Util.mkIff _187_1751))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_187_1752)))
in (FStar_SMTEncoding_Util.mkForall _187_1753))
in ((_187_1754), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (_187_1755))
in (_187_1756)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (let _187_1767 = (let _187_1766 = (let _187_1765 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _187_1764 = (let _187_1763 = (varops.mk_unique "typing_range_const")
in Some (_187_1763))
in ((_187_1765), (Some ("Range_const typing")), (_187_1764))))
in FStar_SMTEncoding_Term.Assume (_187_1766))
in (_187_1767)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _90_2085 -> (match (_90_2085) with
| (l, _90_2084) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_90_2088, f) -> begin
(f env s tt)
end))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _90_2098 = (encode_function_type_as_formula None None t env)
in (match (_90_2098) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _187_1984 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _187_1984)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(

let _90_2108 = (new_term_constant_and_tok_from_lid env lid)
in (match (_90_2108) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match ((let _187_1985 = (FStar_Syntax_Subst.compress t_norm)
in _187_1985.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _90_2111) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _90_2114 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _90_2117 -> begin
[]
end)
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env)))))
end))
end else begin
if (prims.is lid) then begin
(

let vname = (varops.new_fvar lid)
in (

let _90_2124 = (prims.mk lid vname)
in (match (_90_2124) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end else begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let _90_2134 = (

let _90_2129 = (curried_arrow_formals_comp t_norm)
in (match (_90_2129) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _187_1987 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_187_1987)))
end else begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end
end))
in (match (_90_2134) with
| (formals, (pre_opt, res_t)) -> begin
(

let _90_2138 = (new_term_constant_and_tok_from_lid env lid)
in (match (_90_2138) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| _90_2141 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _90_15 -> (match (_90_15) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let _90_2157 = (FStar_Util.prefix vars)
in (match (_90_2157) with
| (_90_2152, (xxsym, _90_2155)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (let _187_2004 = (let _187_2003 = (let _187_2002 = (let _187_2001 = (let _187_2000 = (let _187_1999 = (let _187_1998 = (let _187_1997 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _187_1997))
in ((vapp), (_187_1998)))
in (FStar_SMTEncoding_Util.mkEq _187_1999))
in ((((vapp)::[])::[]), (vars), (_187_2000)))
in (FStar_SMTEncoding_Util.mkForall _187_2001))
in ((_187_2002), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (_187_2003))
in (_187_2004)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let _90_2169 = (FStar_Util.prefix vars)
in (match (_90_2169) with
| (_90_2164, (xxsym, _90_2167)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (let _187_2009 = (let _187_2008 = (let _187_2007 = (let _187_2006 = (let _187_2005 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_187_2005)))
in (FStar_SMTEncoding_Util.mkForall _187_2006))
in ((_187_2007), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (_187_2008))
in (_187_2009)::[])))))
end))
end
| _90_2175 -> begin
[]
end)))))
in (

let _90_2182 = (encode_binders None formals env)
in (match (_90_2182) with
| (vars, guards, env', decls1, _90_2181) -> begin
(

let _90_2191 = (match (pre_opt) with
| None -> begin
(let _187_2010 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((_187_2010), (decls1)))
end
| Some (p) -> begin
(

let _90_2188 = (encode_formula p env')
in (match (_90_2188) with
| (g, ds) -> begin
(let _187_2011 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((_187_2011), ((FStar_List.append decls1 ds))))
end))
end)
in (match (_90_2191) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (let _187_2013 = (let _187_2012 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (_187_2012)))
in (FStar_SMTEncoding_Util.mkApp _187_2013))
in (

let _90_2215 = (

let vname_decl = (let _187_2016 = (let _187_2015 = (FStar_All.pipe_right formals (FStar_List.map (fun _90_2194 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (_187_2015), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_187_2016))
in (

let _90_2202 = (

let env = (

let _90_2197 = env
in {bindings = _90_2197.bindings; depth = _90_2197.depth; tcenv = _90_2197.tcenv; warn = _90_2197.warn; cache = _90_2197.cache; nolabels = _90_2197.nolabels; use_zfuel_name = _90_2197.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_90_2202) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let _90_2212 = (match (formals) with
| [] -> begin
(let _187_2020 = (let _187_2019 = (let _187_2018 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _187_2017 -> Some (_187_2017)) _187_2018))
in (push_free_var env lid vname _187_2019))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_187_2020)))
end
| _90_2206 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (let _187_2021 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) _187_2021))
in (

let name_tok_corr = (let _187_2025 = (let _187_2024 = (let _187_2023 = (let _187_2022 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (_187_2022)))
in (FStar_SMTEncoding_Util.mkForall _187_2023))
in ((_187_2024), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (_187_2025))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (_90_2212) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (_90_2215) with
| (decls2, env) -> begin
(

let _90_2223 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let _90_2219 = (encode_term res_t env')
in (match (_90_2219) with
| (encoded_res_t, decls) -> begin
(let _187_2026 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_187_2026), (decls)))
end)))
in (match (_90_2223) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _187_2030 = (let _187_2029 = (let _187_2028 = (let _187_2027 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_187_2027)))
in (FStar_SMTEncoding_Util.mkForall _187_2028))
in ((_187_2029), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (_187_2030))
in (

let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _187_2036 = (let _187_2033 = (let _187_2032 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _187_2031 = (varops.next_id ())
in ((vname), (_187_2032), (FStar_SMTEncoding_Term.Term_sort), (_187_2031))))
in (FStar_SMTEncoding_Term.fresh_constructor _187_2033))
in (let _187_2035 = (let _187_2034 = (pretype_axiom vapp vars)
in (_187_2034)::[])
in (_187_2036)::_187_2035))
end else begin
[]
end
in (

let g = (let _187_2041 = (let _187_2040 = (let _187_2039 = (let _187_2038 = (let _187_2037 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_187_2037)
in (FStar_List.append freshness _187_2038))
in (FStar_List.append decls3 _187_2039))
in (FStar_List.append decls2 _187_2040))
in (FStar_List.append decls1 _187_2041))
in ((g), (env)))))
end))
end))))
end))
end))))
end))
end)))
end
end))


let declare_top_level_let : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * FStar_SMTEncoding_Term.term Prims.option) * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (match ((try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(

let _90_2234 = (encode_free_var env x t t_norm [])
in (match (_90_2234) with
| (decls, env) -> begin
(

let _90_2239 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_90_2239) with
| (n, x', _90_2238) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, _90_2243) -> begin
((((n), (x))), ([]), (env))
end))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let _90_2253 = (encode_free_var env lid t tt quals)
in (match (_90_2253) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _187_2059 = (let _187_2058 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _187_2058))
in ((_187_2059), (env)))
end else begin
((decls), (env))
end
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _90_2259 lb -> (match (_90_2259) with
| (decls, env) -> begin
(

let _90_2263 = (let _187_2068 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _187_2068 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_90_2263) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env _90_2267 quals -> (match (_90_2267) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _90_2277 = (FStar_Util.first_N nbinders formals)
in (match (_90_2277) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun _90_2281 _90_2285 -> (match (((_90_2281), (_90_2285))) with
| ((formal, _90_2280), (binder, _90_2284)) -> begin
(let _187_2086 = (let _187_2085 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (_187_2085)))
in FStar_Syntax_Syntax.NT (_187_2086))
end)) formals binders)
in (

let extra_formals = (let _187_2090 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _90_2289 -> (match (_90_2289) with
| (x, i) -> begin
(let _187_2089 = (

let _90_2290 = x
in (let _187_2088 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _90_2290.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_2290.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _187_2088}))
in ((_187_2089), (i)))
end))))
in (FStar_All.pipe_right _187_2090 FStar_Syntax_Util.name_binders))
in (

let body = (let _187_2097 = (FStar_Syntax_Subst.compress body)
in (let _187_2096 = (let _187_2091 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _187_2091))
in (let _187_2095 = (let _187_2094 = (let _187_2093 = (FStar_Syntax_Subst.subst subst t)
in _187_2093.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _187_2092 -> Some (_187_2092)) _187_2094))
in (FStar_Syntax_Syntax.extend_app_n _187_2097 _187_2096 _187_2095 body.FStar_Syntax_Syntax.pos))))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (match ((let _187_2108 = (FStar_Syntax_Util.unascribe e)
in _187_2108.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let _90_2309 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_90_2309) with
| (binders, body, opening) -> begin
(match ((let _187_2109 = (FStar_Syntax_Subst.compress t_norm)
in _187_2109.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _90_2316 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_90_2316) with
| (formals, c) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (FStar_Syntax_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c)) then begin
(

let lopt = (subst_lcomp_opt opening lopt)
in (

let _90_2323 = (FStar_Util.first_N nformals binders)
in (match (_90_2323) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun _90_2327 _90_2331 -> (match (((_90_2327), (_90_2331))) with
| ((b, _90_2326), (x, _90_2330)) -> begin
(let _187_2113 = (let _187_2112 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (_187_2112)))
in FStar_Syntax_Syntax.NT (_187_2113))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))), (false))))
end)))
end else begin
if (nformals > nbinders) then begin
(

let _90_2337 = (eta_expand binders formals body tres)
in (match (_90_2337) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end))
end else begin
((((binders), (body), (formals), (tres))), (false))
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _90_2340) -> begin
(let _187_2115 = (let _187_2114 = (aux norm x.FStar_Syntax_Syntax.sort)
in (Prims.fst _187_2114))
in ((_187_2115), (true)))
end
| _90_2344 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _90_2347 -> begin
(let _187_2118 = (let _187_2117 = (FStar_Syntax_Print.term_to_string e)
in (let _187_2116 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _187_2117 _187_2116)))
in (FStar_All.failwith _187_2118))
end)
end))
end
| _90_2349 -> begin
(match ((let _187_2119 = (FStar_Syntax_Subst.compress t_norm)
in _187_2119.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _90_2356 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_90_2356) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let _90_2360 = (eta_expand [] formals e tres)
in (match (_90_2360) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end)))
end))
end
| _90_2362 -> begin
(((([]), (e), ([]), (t_norm))), (false))
end)
end))
in (aux false t_norm)))
in try
(match (()) with
| () -> begin
if (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(

let _90_2390 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _90_2377 lb -> (match (_90_2377) with
| (toks, typs, decls, env) -> begin
(

let _90_2379 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let _90_2385 = (let _187_2124 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _187_2124 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_90_2385) with
| (tok, decl, env) -> begin
(let _187_2127 = (let _187_2126 = (let _187_2125 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((_187_2125), (tok)))
in (_187_2126)::toks)
in ((_187_2127), ((t_norm)::typs), ((decl)::decls), (env)))
end))))
end)) (([]), ([]), ([]), (env))))
in (match (_90_2390) with
| (toks, typs, decls, env) -> begin
(

let toks = (FStar_List.rev toks)
in (

let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs = (FStar_List.rev typs)
in (

let mk_app = (fun curry f ftok vars -> (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
end
| _90_2401 -> begin
if curry then begin
(match (ftok) with
| Some (ftok) -> begin
(mk_Apply ftok vars)
end
| None -> begin
(let _187_2136 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _187_2136 vars))
end)
end else begin
(let _187_2138 = (let _187_2137 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (_187_2137)))
in (FStar_SMTEncoding_Util.mkApp _187_2138))
end
end))
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _90_16 -> (match (_90_16) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _90_2408 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _187_2141 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _187_2141)))))) then begin
((decls), (env))
end else begin
if (not (is_rec)) then begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = _90_2418; FStar_Syntax_Syntax.lbunivs = _90_2416; FStar_Syntax_Syntax.lbtyp = _90_2414; FStar_Syntax_Syntax.lbeff = _90_2412; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _90_2440 = (destruct_bound_function flid t_norm e)
in (match (_90_2440) with
| ((binders, body, _90_2435, _90_2437), curry) -> begin
(

let _90_2447 = (encode_binders None binders env)
in (match (_90_2447) with
| (vars, guards, env', binder_decls, _90_2446) -> begin
(

let app = (mk_app curry f ftok vars)
in (

let _90_2453 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _187_2143 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _187_2142 = (encode_formula body env')
in ((_187_2143), (_187_2142))))
end else begin
(let _187_2144 = (encode_term body env')
in ((app), (_187_2144)))
end
in (match (_90_2453) with
| (app, (body, decls2)) -> begin
(

let eqn = (let _187_2150 = (let _187_2149 = (let _187_2146 = (let _187_2145 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (_187_2145)))
in (FStar_SMTEncoding_Util.mkForall _187_2146))
in (let _187_2148 = (let _187_2147 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_187_2147))
in ((_187_2149), (_187_2148), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (_187_2150))
in (let _187_2155 = (let _187_2154 = (let _187_2153 = (let _187_2152 = (let _187_2151 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) _187_2151))
in (FStar_List.append decls2 _187_2152))
in (FStar_List.append binder_decls _187_2153))
in (FStar_List.append decls _187_2154))
in ((_187_2155), (env))))
end)))
end))
end))))
end
| _90_2456 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _187_2156 = (varops.fresh "fuel")
in ((_187_2156), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env
in (

let _90_2474 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _90_2462 _90_2467 -> (match (((_90_2462), (_90_2467))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (let _187_2159 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar _187_2159))
in (

let gtok = (let _187_2160 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar _187_2160))
in (

let env = (let _187_2163 = (let _187_2162 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _187_2161 -> Some (_187_2161)) _187_2162))
in (push_free_var env flid gtok _187_2163))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (_90_2474) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _90_2483 t_norm _90_2494 -> (match (((_90_2483), (_90_2494))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _90_2493; FStar_Syntax_Syntax.lbunivs = _90_2491; FStar_Syntax_Syntax.lbtyp = _90_2489; FStar_Syntax_Syntax.lbeff = _90_2487; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let _90_2501 = (destruct_bound_function flid t_norm e)
in (match (_90_2501) with
| ((binders, body, formals, tres), curry) -> begin
(

let _90_2502 = if curry then begin
(FStar_All.failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end else begin
()
end
in (

let _90_2510 = (encode_binders None binders env)
in (match (_90_2510) with
| (vars, guards, env', binder_decls, _90_2509) -> begin
(

let decl_g = (let _187_2174 = (let _187_2173 = (let _187_2172 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_187_2172)
in ((g), (_187_2173), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (_187_2174))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (let _187_2176 = (let _187_2175 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (_187_2175)))
in (FStar_SMTEncoding_Util.mkApp _187_2176))
in (

let gsapp = (let _187_2179 = (let _187_2178 = (let _187_2177 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_187_2177)::vars_tm)
in ((g), (_187_2178)))
in (FStar_SMTEncoding_Util.mkApp _187_2179))
in (

let gmax = (let _187_2182 = (let _187_2181 = (let _187_2180 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (_187_2180)::vars_tm)
in ((g), (_187_2181)))
in (FStar_SMTEncoding_Util.mkApp _187_2182))
in (

let _90_2520 = (encode_term body env')
in (match (_90_2520) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _187_2188 = (let _187_2187 = (let _187_2184 = (let _187_2183 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (_187_2183)))
in (FStar_SMTEncoding_Util.mkForall' _187_2184))
in (let _187_2186 = (let _187_2185 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_187_2185))
in ((_187_2187), (_187_2186), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (_187_2188))
in (

let eqn_f = (let _187_2192 = (let _187_2191 = (let _187_2190 = (let _187_2189 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_187_2189)))
in (FStar_SMTEncoding_Util.mkForall _187_2190))
in ((_187_2191), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_187_2192))
in (

let eqn_g' = (let _187_2201 = (let _187_2200 = (let _187_2199 = (let _187_2198 = (let _187_2197 = (let _187_2196 = (let _187_2195 = (let _187_2194 = (let _187_2193 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (_187_2193)::vars_tm)
in ((g), (_187_2194)))
in (FStar_SMTEncoding_Util.mkApp _187_2195))
in ((gsapp), (_187_2196)))
in (FStar_SMTEncoding_Util.mkEq _187_2197))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_187_2198)))
in (FStar_SMTEncoding_Util.mkForall _187_2199))
in ((_187_2200), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (_187_2201))
in (

let _90_2543 = (

let _90_2530 = (encode_binders None formals env0)
in (match (_90_2530) with
| (vars, v_guards, env, binder_decls, _90_2529) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (let _187_2202 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _187_2202 ((fuel)::vars)))
in (let _187_2206 = (let _187_2205 = (let _187_2204 = (let _187_2203 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_187_2203)))
in (FStar_SMTEncoding_Util.mkForall _187_2204))
in ((_187_2205), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (_187_2206)))
in (

let _90_2540 = (

let _90_2537 = (encode_term_pred None tres env gapp)
in (match (_90_2537) with
| (g_typing, d3) -> begin
(let _187_2214 = (let _187_2213 = (let _187_2212 = (let _187_2211 = (let _187_2210 = (let _187_2209 = (let _187_2208 = (let _187_2207 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((_187_2207), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp _187_2208))
in ((((gapp)::[])::[]), ((fuel)::vars), (_187_2209)))
in (FStar_SMTEncoding_Util.mkForall _187_2210))
in ((_187_2211), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_187_2212))
in (_187_2213)::[])
in ((d3), (_187_2214)))
end))
in (match (_90_2540) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (_90_2543) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end)))
end))
end))
in (

let _90_2559 = (let _187_2217 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _90_2547 _90_2551 -> (match (((_90_2547), (_90_2551))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _90_2555 = (encode_one_binding env0 gtok ty bs)
in (match (_90_2555) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _187_2217))
in (match (_90_2559) with
| (decls, eqns, env0) -> begin
(

let _90_2568 = (let _187_2219 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _187_2219 (FStar_List.partition (fun _90_17 -> (match (_90_17) with
| FStar_SMTEncoding_Term.DeclFun (_90_2562) -> begin
true
end
| _90_2565 -> begin
false
end)))))
in (match (_90_2568) with
| (prefix_decls, rest) -> begin
(

let eqns = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns))), (env0)))
end))
end))))
end)))))
end
end))))
end))
end
end)
with
| Let_rec_unencodeable -> begin
(

let msg = (let _187_2222 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _187_2222 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let _90_2572 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _187_2231 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _187_2231))
end else begin
()
end
in (

let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (

let _90_2580 = (encode_sigelt' env se)
in (match (_90_2580) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _187_2234 = (let _187_2233 = (let _187_2232 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_187_2232))
in (_187_2233)::[])
in ((_187_2234), (e)))
end
| _90_2583 -> begin
(let _187_2241 = (let _187_2240 = (let _187_2236 = (let _187_2235 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_187_2235))
in (_187_2236)::g)
in (let _187_2239 = (let _187_2238 = (let _187_2237 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_187_2237))
in (_187_2238)::[])
in (FStar_List.append _187_2240 _187_2239)))
in ((_187_2241), (e)))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_90_2589) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _90_2605) -> begin
if (let _187_2246 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _187_2246 Prims.op_Negation)) then begin
(([]), (env))
end else begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| _90_2612 -> begin
(let _187_2252 = (let _187_2251 = (let _187_2250 = (FStar_All.pipe_left (fun _187_2249 -> Some (_187_2249)) (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (_187_2250)))
in FStar_Syntax_Syntax.Tm_abs (_187_2251))
in (FStar_Syntax_Syntax.mk _187_2252 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env a -> (

let _90_2619 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (_90_2619) with
| (aname, atok, env) -> begin
(

let _90_2623 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (_90_2623) with
| (formals, _90_2622) -> begin
(

let _90_2626 = (let _187_2257 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term _187_2257 env))
in (match (_90_2626) with
| (tm, decls) -> begin
(

let a_decls = (let _187_2261 = (let _187_2260 = (let _187_2259 = (FStar_All.pipe_right formals (FStar_List.map (fun _90_2627 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (_187_2259), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (_187_2260))
in (_187_2261)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let _90_2641 = (let _187_2263 = (FStar_All.pipe_right formals (FStar_List.map (fun _90_2633 -> (match (_90_2633) with
| (bv, _90_2632) -> begin
(

let _90_2638 = (gen_term_var env bv)
in (match (_90_2638) with
| (xxsym, xx, _90_2637) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right _187_2263 FStar_List.split))
in (match (_90_2641) with
| (xs_sorts, xs) -> begin
(

let app = (let _187_2266 = (let _187_2265 = (let _187_2264 = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (_187_2264)::[])
in (("Reify"), (_187_2265)))
in (FStar_SMTEncoding_Util.mkApp _187_2266))
in (

let a_eq = (let _187_2272 = (let _187_2271 = (let _187_2270 = (let _187_2269 = (let _187_2268 = (let _187_2267 = (mk_Apply tm xs_sorts)
in ((app), (_187_2267)))
in (FStar_SMTEncoding_Util.mkEq _187_2268))
in ((((app)::[])::[]), (xs_sorts), (_187_2269)))
in (FStar_SMTEncoding_Util.mkForall _187_2270))
in ((_187_2271), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (_187_2272))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (let _187_2276 = (let _187_2275 = (let _187_2274 = (let _187_2273 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (_187_2273)))
in (FStar_SMTEncoding_Util.mkForall _187_2274))
in ((_187_2275), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (_187_2276))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let _90_2649 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (_90_2649) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _90_2652, _90_2654, _90_2656, _90_2658) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let _90_2664 = (new_term_constant_and_tok_from_lid env lid)
in (match (_90_2664) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _90_2667, t, quals, _90_2671) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _90_18 -> (match (_90_18) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _90_2684 -> begin
false
end))))))
in if will_encode_definition then begin
(([]), (env))
end else begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let _90_2689 = (encode_top_level_val env fv t quals)
in (match (_90_2689) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (let _187_2279 = (let _187_2278 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _187_2278))
in ((_187_2279), (env)))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _90_2695, _90_2697) -> begin
(

let _90_2702 = (encode_formula f env)
in (match (_90_2702) with
| (f, decls) -> begin
(

let g = (let _187_2286 = (let _187_2285 = (let _187_2284 = (let _187_2281 = (let _187_2280 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _187_2280))
in Some (_187_2281))
in (let _187_2283 = (let _187_2282 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (_187_2282))
in ((f), (_187_2284), (_187_2283))))
in FStar_SMTEncoding_Term.Assume (_187_2285))
in (_187_2286)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _90_2707, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let _90_2720 = (FStar_Util.fold_map (fun env lb -> (

let lid = (let _187_2290 = (let _187_2289 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _187_2289.FStar_Syntax_Syntax.fv_name)
in _187_2290.FStar_Syntax_Syntax.v)
in if (let _187_2291 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _187_2291)) then begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let _90_2717 = (encode_sigelt' env val_decl)
in (match (_90_2717) with
| (decls, env) -> begin
((env), (decls))
end)))
end else begin
((env), ([]))
end)) env (Prims.snd lbs))
in (match (_90_2720) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((_90_2722, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _90_2730; FStar_Syntax_Syntax.lbtyp = _90_2728; FStar_Syntax_Syntax.lbeff = _90_2726; FStar_Syntax_Syntax.lbdef = _90_2724})::[]), _90_2737, _90_2739, _90_2741) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let _90_2747 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_90_2747) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid_b2t_x = (let _187_2294 = (let _187_2293 = (let _187_2292 = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (_187_2292)::[])
in (("Valid"), (_187_2293)))
in (FStar_SMTEncoding_Util.mkApp _187_2294))
in (

let decls = (let _187_2302 = (let _187_2301 = (let _187_2300 = (let _187_2299 = (let _187_2298 = (let _187_2297 = (let _187_2296 = (let _187_2295 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_187_2295)))
in (FStar_SMTEncoding_Util.mkEq _187_2296))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_187_2297)))
in (FStar_SMTEncoding_Util.mkForall _187_2298))
in ((_187_2299), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (_187_2300))
in (_187_2301)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::_187_2302)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_90_2753, _90_2755, _90_2757, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _90_19 -> (match (_90_19) with
| FStar_Syntax_Syntax.Discriminator (_90_2763) -> begin
true
end
| _90_2766 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (_90_2768, _90_2770, lids, quals) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> ((let _187_2305 = (FStar_List.hd l.FStar_Ident.ns)
in _187_2305.FStar_Ident.idText) = "Prims")))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _90_20 -> (match (_90_20) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| _90_2779 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _90_2785, _90_2787, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _90_21 -> (match (_90_21) with
| FStar_Syntax_Syntax.Projector (_90_2793) -> begin
true
end
| _90_2796 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_90_2800) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _90_2809, _90_2811, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(match ((let _187_2308 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in _187_2308.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _90_2818) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None)))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let _90_2826 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (_90_2826) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let _90_2827 = env.tcenv
in {FStar_TypeChecker_Env.solver = _90_2827.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _90_2827.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _90_2827.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _90_2827.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _90_2827.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _90_2827.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _90_2827.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _90_2827.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _90_2827.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _90_2827.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _90_2827.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _90_2827.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _90_2827.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _90_2827.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _90_2827.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _90_2827.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _90_2827.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _90_2827.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = _90_2827.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = _90_2827.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _90_2827.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _90_2827.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _90_2827.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (let _187_2309 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals _187_2309)))
end))
in (

let lb = (

let _90_2831 = lb
in {FStar_Syntax_Syntax.lbname = _90_2831.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _90_2831.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = _90_2831.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (encode_top_level_let env ((false), ((lb)::[])) quals))))))
end
| _90_2835 -> begin
(([]), (env))
end)
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _90_2840, _90_2842, quals) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _90_2848, _90_2850, _90_2852) -> begin
(

let _90_2857 = (encode_signature env ses)
in (match (_90_2857) with
| (g, env) -> begin
(

let _90_2871 = (FStar_All.pipe_right g (FStar_List.partition (fun _90_22 -> (match (_90_22) with
| FStar_SMTEncoding_Term.Assume (_90_2860, Some ("inversion axiom"), _90_2864) -> begin
false
end
| _90_2868 -> begin
true
end))))
in (match (_90_2871) with
| (g', inversions) -> begin
(

let _90_2880 = (FStar_All.pipe_right g' (FStar_List.partition (fun _90_23 -> (match (_90_23) with
| FStar_SMTEncoding_Term.DeclFun (_90_2874) -> begin
true
end
| _90_2877 -> begin
false
end))))
in (match (_90_2880) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _90_2883, tps, k, _90_2887, datas, quals, _90_2891) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _90_24 -> (match (_90_24) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _90_2898 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _90_2910 = c
in (match (_90_2910) with
| (name, args, _90_2905, _90_2907, _90_2909) -> begin
(let _187_2317 = (let _187_2316 = (let _187_2315 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_187_2315), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_187_2316))
in (_187_2317)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _187_2323 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _187_2323 FStar_Option.isNone))))) then begin
[]
end else begin
(

let _90_2917 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_90_2917) with
| (xxsym, xx) -> begin
(

let _90_2953 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _90_2920 l -> (match (_90_2920) with
| (out, decls) -> begin
(

let _90_2925 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_90_2925) with
| (_90_2923, data_t) -> begin
(

let _90_2928 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_90_2928) with
| (args, res) -> begin
(

let indices = (match ((let _187_2326 = (FStar_Syntax_Subst.compress res)
in _187_2326.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_90_2930, indices) -> begin
indices
end
| _90_2935 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _90_2941 -> (match (_90_2941) with
| (x, _90_2940) -> begin
(let _187_2331 = (let _187_2330 = (let _187_2329 = (mk_term_projector_name l x)
in ((_187_2329), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp _187_2330))
in (push_term_var env x _187_2331))
end)) env))
in (

let _90_2945 = (encode_args indices env)
in (match (_90_2945) with
| (indices, decls') -> begin
(

let _90_2946 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _187_2336 = (FStar_List.map2 (fun v a -> (let _187_2335 = (let _187_2334 = (FStar_SMTEncoding_Util.mkFreeV v)
in ((_187_2334), (a)))
in (FStar_SMTEncoding_Util.mkEq _187_2335))) vars indices)
in (FStar_All.pipe_right _187_2336 FStar_SMTEncoding_Util.mk_and_l))
in (let _187_2341 = (let _187_2340 = (let _187_2339 = (let _187_2338 = (let _187_2337 = (mk_data_tester env l xx)
in ((_187_2337), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd _187_2338))
in ((out), (_187_2339)))
in (FStar_SMTEncoding_Util.mkOr _187_2340))
in ((_187_2341), ((FStar_List.append decls decls'))))))
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (_90_2953) with
| (data_ax, decls) -> begin
(

let _90_2956 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_90_2956) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = if ((FStar_List.length datas) > (Prims.parse_int "1")) then begin
(let _187_2342 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _187_2342 xx tapp))
end else begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end
in (let _187_2349 = (let _187_2348 = (let _187_2345 = (let _187_2344 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _187_2343 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (_187_2344), (_187_2343))))
in (FStar_SMTEncoding_Util.mkForall _187_2345))
in (let _187_2347 = (let _187_2346 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (_187_2346))
in ((_187_2348), (Some ("inversion axiom")), (_187_2347))))
in FStar_SMTEncoding_Term.Assume (_187_2349)))
in (

let pattern_guarded_inversion = if ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1"))) then begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (let _187_2357 = (let _187_2356 = (let _187_2355 = (let _187_2352 = (let _187_2351 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _187_2350 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (_187_2351), (_187_2350))))
in (FStar_SMTEncoding_Util.mkForall _187_2352))
in (let _187_2354 = (let _187_2353 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (_187_2353))
in ((_187_2355), (Some ("inversion axiom")), (_187_2354))))
in FStar_SMTEncoding_Term.Assume (_187_2356))
in (_187_2357)::[])))
end else begin
[]
end
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)
in (

let _90_2970 = (match ((let _187_2358 = (FStar_Syntax_Subst.compress k)
in _187_2358.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| _90_2967 -> begin
((tps), (k))
end)
in (match (_90_2970) with
| (formals, res) -> begin
(

let _90_2973 = (FStar_Syntax_Subst.open_term formals res)
in (match (_90_2973) with
| (formals, res) -> begin
(

let _90_2980 = (encode_binders None formals env)
in (match (_90_2980) with
| (vars, guards, env', binder_decls, _90_2979) -> begin
(

let _90_2984 = (new_term_constant_and_tok_from_lid env t)
in (match (_90_2984) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (let _187_2360 = (let _187_2359 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (_187_2359)))
in (FStar_SMTEncoding_Util.mkApp _187_2360))
in (

let _90_3005 = (

let tname_decl = (let _187_2364 = (let _187_2363 = (FStar_All.pipe_right vars (FStar_List.map (fun _90_2990 -> (match (_90_2990) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _187_2362 = (varops.next_id ())
in ((tname), (_187_2363), (FStar_SMTEncoding_Term.Term_sort), (_187_2362), (false))))
in (constructor_or_logic_type_decl _187_2364))
in (

let _90_3002 = (match (vars) with
| [] -> begin
(let _187_2368 = (let _187_2367 = (let _187_2366 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _187_2365 -> Some (_187_2365)) _187_2366))
in (push_free_var env t tname _187_2367))
in (([]), (_187_2368)))
end
| _90_2994 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (let _187_2369 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) _187_2369))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _187_2373 = (let _187_2372 = (let _187_2371 = (let _187_2370 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_187_2370)))
in (FStar_SMTEncoding_Util.mkForall' _187_2371))
in ((_187_2372), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_187_2373))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (_90_3002) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (_90_3005) with
| (decls, env) -> begin
(

let kindingAx = (

let _90_3008 = (encode_term_pred None res env' tapp)
in (match (_90_3008) with
| (k, decls) -> begin
(

let karr = if ((FStar_List.length formals) > (Prims.parse_int "0")) then begin
(let _187_2377 = (let _187_2376 = (let _187_2375 = (let _187_2374 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _187_2374))
in ((_187_2375), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_187_2376))
in (_187_2377)::[])
end else begin
[]
end
in (let _187_2384 = (let _187_2383 = (let _187_2382 = (let _187_2381 = (let _187_2380 = (let _187_2379 = (let _187_2378 = (FStar_SMTEncoding_Util.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_187_2378)))
in (FStar_SMTEncoding_Util.mkForall _187_2379))
in ((_187_2380), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_187_2381))
in (_187_2382)::[])
in (FStar_List.append karr _187_2383))
in (FStar_List.append decls _187_2384)))
end))
in (

let aux = (let _187_2388 = (let _187_2387 = (inversion_axioms tapp vars)
in (let _187_2386 = (let _187_2385 = (pretype_axiom tapp vars)
in (_187_2385)::[])
in (FStar_List.append _187_2387 _187_2386)))
in (FStar_List.append kindingAx _187_2388))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _90_3015, _90_3017, _90_3019, _90_3021, _90_3023, _90_3025, _90_3027) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _90_3032, t, _90_3035, n_tps, quals, _90_3039, drange) -> begin
(

let _90_3046 = (new_term_constant_and_tok_from_lid env d)
in (match (_90_3046) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let _90_3050 = (FStar_Syntax_Util.arrow_formals t)
in (match (_90_3050) with
| (formals, t_res) -> begin
(

let _90_3053 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_90_3053) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let _90_3060 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_90_3060) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _187_2390 = (mk_term_projector_name d x)
in ((_187_2390), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (let _187_2392 = (let _187_2391 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (_187_2391), (true)))
in (FStar_All.pipe_right _187_2392 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let _90_3070 = (encode_term_pred None t env ddtok_tm)
in (match (_90_3070) with
| (tok_typing, decls3) -> begin
(

let _90_3077 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_90_3077) with
| (vars', guards', env'', decls_formals, _90_3076) -> begin
(

let _90_3082 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_90_3082) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _90_3086 -> begin
(let _187_2394 = (let _187_2393 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) _187_2393))
in (_187_2394)::[])
end)
in (

let encode_elim = (fun _90_3089 -> (match (()) with
| () -> begin
(

let _90_3092 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_90_3092) with
| (head, args) -> begin
(match ((let _187_2397 = (FStar_Syntax_Subst.compress head)
in _187_2397.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let _90_3110 = (encode_args args env')
in (match (_90_3110) with
| (encoded_args, arg_decls) -> begin
(

let _90_3125 = (FStar_List.fold_left (fun _90_3114 arg -> (match (_90_3114) with
| (env, arg_vars, eqns) -> begin
(

let _90_3120 = (let _187_2400 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _187_2400))
in (match (_90_3120) with
| (_90_3117, xv, env) -> begin
(let _187_2402 = (let _187_2401 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (_187_2401)::eqns)
in ((env), ((xv)::arg_vars), (_187_2402)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (_90_3125) with
| (_90_3122, arg_vars, eqns) -> begin
(

let arg_vars = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_Util.mkApp ((encoded_head), (arg_vars)))
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (

let typing_inversion = (let _187_2409 = (let _187_2408 = (let _187_2407 = (let _187_2406 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _187_2405 = (let _187_2404 = (let _187_2403 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_187_2403)))
in (FStar_SMTEncoding_Util.mkImp _187_2404))
in ((((ty_pred)::[])::[]), (_187_2406), (_187_2405))))
in (FStar_SMTEncoding_Util.mkForall _187_2407))
in ((_187_2408), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_187_2409))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(

let x = (let _187_2410 = (varops.fresh "x")
in ((_187_2410), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (let _187_2422 = (let _187_2421 = (let _187_2418 = (let _187_2417 = (let _187_2412 = (let _187_2411 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in (_187_2411)::[])
in (_187_2412)::[])
in (let _187_2416 = (let _187_2415 = (let _187_2414 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _187_2413 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in ((_187_2414), (_187_2413))))
in (FStar_SMTEncoding_Util.mkImp _187_2415))
in ((_187_2417), ((x)::[]), (_187_2416))))
in (FStar_SMTEncoding_Util.mkForall _187_2418))
in (let _187_2420 = (let _187_2419 = (varops.mk_unique "lextop")
in Some (_187_2419))
in ((_187_2421), (Some ("lextop is top")), (_187_2420))))
in FStar_SMTEncoding_Term.Assume (_187_2422))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _187_2425 = (let _187_2424 = (FStar_SMTEncoding_Util.mkFreeV v)
in (FStar_SMTEncoding_Util.mk_Precedes _187_2424 dapp))
in (_187_2425)::[])
end
| _90_3139 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _187_2432 = (let _187_2431 = (let _187_2430 = (let _187_2429 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _187_2428 = (let _187_2427 = (let _187_2426 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (_187_2426)))
in (FStar_SMTEncoding_Util.mkImp _187_2427))
in ((((ty_pred)::[])::[]), (_187_2429), (_187_2428))))
in (FStar_SMTEncoding_Util.mkForall _187_2430))
in ((_187_2431), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_187_2432)))
end
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| _90_3143 -> begin
(

let _90_3144 = (let _187_2435 = (let _187_2434 = (FStar_Syntax_Print.lid_to_string d)
in (let _187_2433 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _187_2434 _187_2433)))
in (FStar_TypeChecker_Errors.warn drange _187_2435))
in (([]), ([])))
end)
end))
end))
in (

let _90_3148 = (encode_elim ())
in (match (_90_3148) with
| (decls2, elim) -> begin
(

let g = (let _187_2462 = (let _187_2461 = (let _187_2460 = (let _187_2459 = (let _187_2440 = (let _187_2439 = (let _187_2438 = (let _187_2437 = (let _187_2436 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _187_2436))
in Some (_187_2437))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (_187_2438)))
in FStar_SMTEncoding_Term.DeclFun (_187_2439))
in (_187_2440)::[])
in (let _187_2458 = (let _187_2457 = (let _187_2456 = (let _187_2455 = (let _187_2454 = (let _187_2453 = (let _187_2452 = (let _187_2444 = (let _187_2443 = (let _187_2442 = (let _187_2441 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_187_2441)))
in (FStar_SMTEncoding_Util.mkForall _187_2442))
in ((_187_2443), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_187_2444))
in (let _187_2451 = (let _187_2450 = (let _187_2449 = (let _187_2448 = (let _187_2447 = (let _187_2446 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (let _187_2445 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_187_2446), (_187_2445))))
in (FStar_SMTEncoding_Util.mkForall _187_2447))
in ((_187_2448), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_187_2449))
in (_187_2450)::[])
in (_187_2452)::_187_2451))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::_187_2453)
in (FStar_List.append _187_2454 elim))
in (FStar_List.append decls_pred _187_2455))
in (FStar_List.append decls_formals _187_2456))
in (FStar_List.append proxy_fresh _187_2457))
in (FStar_List.append _187_2459 _187_2458)))
in (FStar_List.append decls3 _187_2460))
in (FStar_List.append decls2 _187_2461))
in (FStar_List.append binder_decls _187_2462))
in (((FStar_List.append datacons g)), (env)))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end))
end)))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _90_3154 se -> (match (_90_3154) with
| (g, env) -> begin
(

let _90_3158 = (encode_sigelt env se)
in (match (_90_3158) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b _90_3166 -> (match (_90_3166) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_90_3168) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let _90_3173 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _187_2477 = (FStar_Syntax_Print.bv_to_string x)
in (let _187_2476 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _187_2475 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _187_2477 _187_2476 _187_2475))))
end else begin
()
end
in (

let _90_3177 = (encode_term t1 env)
in (match (_90_3177) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let _90_3182 = (let _187_2482 = (let _187_2481 = (let _187_2480 = (FStar_Util.digest_of_string t_hash)
in (let _187_2479 = (let _187_2478 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _187_2478))
in (Prims.strcat _187_2480 _187_2479)))
in (Prims.strcat "x_" _187_2481))
in (new_term_constant_from_string env x _187_2482))
in (match (_90_3182) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _187_2486 = (let _187_2485 = (FStar_Syntax_Print.bv_to_string x)
in (let _187_2484 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _187_2483 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _187_2485 _187_2484 _187_2483))))
in Some (_187_2486))
end else begin
None
end
in (

let ax = (

let a_name = Some ((Prims.strcat "binder_" xxsym))
in FStar_SMTEncoding_Term.Assume (((t), (a_name), (a_name))))
in (

let g = (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun (((xxsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((ax)::[])))
in (((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))))))
end)))
end))))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_90_3190, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let _90_3199 = (encode_free_var env fv t t_norm [])
in (match (_90_3199) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let _90_3213 = (encode_sigelt env se)
in (match (_90_3213) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let _90_3218 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (_90_3218) with
| (_90_3215, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _90_3225 -> (match (_90_3225) with
| (l, _90_3222, _90_3224) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _90_3232 -> (match (_90_3232) with
| (l, _90_3229, _90_3231) -> begin
(let _187_2494 = (FStar_All.pipe_left (fun _187_2490 -> FStar_SMTEncoding_Term.Echo (_187_2490)) (Prims.fst l))
in (let _187_2493 = (let _187_2492 = (let _187_2491 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_187_2491))
in (_187_2492)::[])
in (_187_2494)::_187_2493))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _187_2499 = (let _187_2498 = (let _187_2497 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = _187_2497; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_187_2498)::[])
in (FStar_ST.op_Colon_Equals last_env _187_2499)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_90_3238 -> begin
(

let _90_3241 = e
in {bindings = _90_3241.bindings; depth = _90_3241.depth; tcenv = tcenv; warn = _90_3241.warn; cache = _90_3241.cache; nolabels = _90_3241.nolabels; use_zfuel_name = _90_3241.use_zfuel_name; encode_non_total_function_typ = _90_3241.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_90_3247)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _90_3249 -> (match (()) with
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

let _90_3255 = hd
in {bindings = _90_3255.bindings; depth = _90_3255.depth; tcenv = _90_3255.tcenv; warn = _90_3255.warn; cache = refs; nolabels = _90_3255.nolabels; use_zfuel_name = _90_3255.use_zfuel_name; encode_non_total_function_typ = _90_3255.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _90_3258 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_90_3262)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _90_3264 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _90_3265 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _90_3266 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_90_3269)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _90_3274 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let _90_3276 = (init_env tcenv)
in (

let _90_3278 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _90_3281 = (push_env ())
in (

let _90_3283 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _90_3286 = (let _187_2520 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _187_2520))
in (

let _90_3288 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _90_3291 = (mark_env ())
in (

let _90_3293 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _90_3296 = (reset_mark_env ())
in (

let _90_3298 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _90_3301 = (commit_mark_env ())
in (

let _90_3303 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _187_2536 = (let _187_2535 = (let _187_2534 = (let _187_2533 = (let _187_2532 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _187_2532 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _187_2533 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _187_2534))
in FStar_SMTEncoding_Term.Caption (_187_2535))
in (_187_2536)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _90_3312 = (encode_sigelt env se)
in (match (_90_3312) with
| (decls, env) -> begin
(

let _90_3313 = (set_env env)
in (let _187_2537 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _187_2537)))
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let _90_3318 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _187_2542 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _187_2542))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _90_3325 = (encode_signature (

let _90_3321 = env
in {bindings = _90_3321.bindings; depth = _90_3321.depth; tcenv = _90_3321.tcenv; warn = false; cache = _90_3321.cache; nolabels = _90_3321.nolabels; use_zfuel_name = _90_3321.use_zfuel_name; encode_non_total_function_typ = _90_3321.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_90_3325) with
| (decls, env) -> begin
(

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (

let _90_3331 = (set_env (

let _90_3329 = env
in {bindings = _90_3329.bindings; depth = _90_3329.depth; tcenv = _90_3329.tcenv; warn = true; cache = _90_3329.cache; nolabels = _90_3329.nolabels; use_zfuel_name = _90_3329.use_zfuel_name; encode_non_total_function_typ = _90_3329.encode_non_total_function_typ}))
in (

let _90_3333 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> (

let _90_3339 = (let _187_2560 = (let _187_2559 = (FStar_TypeChecker_Env.current_module tcenv)
in _187_2559.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name _187_2560))
in (

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let _90_3364 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let _90_3353 = (aux rest)
in (match (_90_3353) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _187_2566 = (let _187_2565 = (FStar_Syntax_Syntax.mk_binder (

let _90_3355 = x
in {FStar_Syntax_Syntax.ppname = _90_3355.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _90_3355.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_187_2565)::out)
in ((_187_2566), (rest))))
end))
end
| _90_3358 -> begin
(([]), (bindings))
end))
in (

let _90_3361 = (aux bindings)
in (match (_90_3361) with
| (closing, bindings) -> begin
(let _187_2567 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((_187_2567), (bindings)))
end)))
in (match (_90_3364) with
| (q, bindings) -> begin
(

let _90_3373 = (let _187_2569 = (FStar_List.filter (fun _90_25 -> (match (_90_25) with
| FStar_TypeChecker_Env.Binding_sig (_90_3367) -> begin
false
end
| _90_3370 -> begin
true
end)) bindings)
in (encode_env_bindings env _187_2569))
in (match (_90_3373) with
| (env_decls, env) -> begin
(

let _90_3374 = if (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery")))) then begin
(let _187_2570 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _187_2570))
end else begin
()
end
in (

let _90_3378 = (encode_formula q env)
in (match (_90_3378) with
| (phi, qdecls) -> begin
(

let _90_3381 = (let _187_2571 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _187_2571 phi))
in (match (_90_3381) with
| (labels, phi) -> begin
(

let _90_3384 = (encode_labels labels)
in (match (_90_3384) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (let _187_2575 = (let _187_2574 = (FStar_SMTEncoding_Util.mkNot phi)
in (let _187_2573 = (let _187_2572 = (varops.mk_unique "@query")
in Some (_187_2572))
in ((_187_2574), (Some ("query")), (_187_2573))))
in FStar_SMTEncoding_Term.Assume (_187_2575))
in (

let suffix = (let _187_2577 = (let _187_2576 = if (FStar_Options.print_z3_statistics ()) then begin
(FStar_SMTEncoding_Term.PrintStats)::[]
end else begin
[]
end
in (FStar_List.append _187_2576 ((FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in (FStar_List.append label_suffix _187_2577))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end))
end)))
end))
end))))))


let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (

let env = (get_env tcenv)
in (

let _90_3391 = (push "query")
in (

let _90_3396 = (encode_formula q env)
in (match (_90_3396) with
| (f, _90_3395) -> begin
(

let _90_3397 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _90_3401) -> begin
true
end
| _90_3405 -> begin
false
end))
end)))))






open Prims

let add_fuel = (fun x tl -> if (FStar_Options.unthrottle_inductives ()) then begin
tl
end else begin
(x)::tl
end)


let withenv = (fun c _85_30 -> (match (_85_30) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun _85_1 -> (match (_85_1) with
| (FStar_Util.Inl (_85_34), _85_37) -> begin
false
end
| _85_40 -> begin
true
end)) args))


let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l)) -> begin
(let _177_12 = (let _177_11 = (let _177_10 = (let _177_9 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _177_9))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _177_10))
in FStar_Util.Inl (_177_11))
in Some (_177_12))
end
| _85_47 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a = (

let _85_51 = a
in (let _177_19 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _177_19; FStar_Syntax_Syntax.index = _85_51.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _85_51.FStar_Syntax_Syntax.sort}))
in (let _177_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _177_20))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun _85_58 -> (match (()) with
| () -> begin
(let _177_30 = (let _177_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _177_29 lid.FStar_Ident.str))
in (FStar_All.failwith _177_30))
end))
in (

let _85_62 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_85_62) with
| (_85_60, t) -> begin
(match ((let _177_31 = (FStar_Syntax_Subst.compress t)
in _177_31.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let _85_70 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_85_70) with
| (binders, _85_69) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end
end))
end
| _85_73 -> begin
(fail ())
end)
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _177_37 = (let _177_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _177_36))
in (FStar_All.pipe_left escape _177_37)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _177_43 = (let _177_42 = (mk_term_projector_name lid a)
in ((_177_42), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Term.mkFreeV _177_43)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _177_49 = (let _177_48 = (mk_term_projector_name_by_pos lid i)
in ((_177_48), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Term.mkFreeV _177_49)))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))


type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int}


let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))


let varops : varops_t = (

let initial_ctr = 100
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun _85_97 -> (match (()) with
| () -> begin
(let _177_153 = (FStar_Util.smap_create 100)
in (let _177_152 = (FStar_Util.smap_create 100)
in ((_177_153), (_177_152))))
end))
in (

let scopes = (let _177_155 = (let _177_154 = (new_scope ())
in (_177_154)::[])
in (FStar_Util.mk_ref _177_155))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (match ((let _177_159 = (FStar_ST.read scopes)
in (FStar_Util.find_map _177_159 (fun _85_105 -> (match (_85_105) with
| (names, _85_104) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_85_108) -> begin
(

let _85_110 = (FStar_Util.incr ctr)
in (let _177_162 = (let _177_161 = (let _177_160 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _177_160))
in (Prims.strcat "__" _177_161))
in (Prims.strcat y _177_162)))
end)
in (

let top_scope = (let _177_164 = (let _177_163 = (FStar_ST.read scopes)
in (FStar_List.hd _177_163))
in (FStar_All.pipe_left Prims.fst _177_164))
in (

let _85_114 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (

let new_var = (fun pp rn -> (let _177_171 = (let _177_170 = (let _177_169 = (FStar_Util.string_of_int rn)
in (Prims.strcat "__" _177_169))
in (Prims.strcat pp.FStar_Ident.idText _177_170))
in (FStar_All.pipe_left mk_unique _177_171)))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun _85_122 -> (match (()) with
| () -> begin
(

let _85_123 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (

let fresh = (fun pfx -> (let _177_179 = (let _177_178 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _177_178))
in (FStar_Util.format2 "%s_%s" pfx _177_179)))
in (

let string_const = (fun s -> (match ((let _177_183 = (FStar_ST.read scopes)
in (FStar_Util.find_map _177_183 (fun _85_132 -> (match (_85_132) with
| (_85_130, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (let _177_184 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _177_184))
in (

let top_scope = (let _177_186 = (let _177_185 = (FStar_ST.read scopes)
in (FStar_List.hd _177_185))
in (FStar_All.pipe_left Prims.snd _177_186))
in (

let _85_139 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (

let push = (fun _85_142 -> (match (()) with
| () -> begin
(let _177_191 = (let _177_190 = (new_scope ())
in (let _177_189 = (FStar_ST.read scopes)
in (_177_190)::_177_189))
in (FStar_ST.op_Colon_Equals scopes _177_191))
end))
in (

let pop = (fun _85_144 -> (match (()) with
| () -> begin
(let _177_195 = (let _177_194 = (FStar_ST.read scopes)
in (FStar_List.tl _177_194))
in (FStar_ST.op_Colon_Equals scopes _177_195))
end))
in (

let mark = (fun _85_146 -> (match (()) with
| () -> begin
(push ())
end))
in (

let reset_mark = (fun _85_148 -> (match (()) with
| () -> begin
(pop ())
end))
in (

let commit_mark = (fun _85_150 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
(

let _85_163 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (

let _85_168 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes ((((next1), (next2)))::tl))))
end
| _85_171 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let _85_173 = x
in (let _177_210 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _177_210; FStar_Syntax_Syntax.index = _85_173.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _85_173.FStar_Syntax_Syntax.sort})))


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
| Binding_var (_85_177) -> begin
_85_177
end))


let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_85_180) -> begin
_85_180
end))


let binder_of_eithervar = (fun v -> ((v), (None)))


type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))


let print_env : env_t  ->  Prims.string = (fun e -> (let _177_268 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _85_2 -> (match (_85_2) with
| Binding_var (x, _85_195) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _85_200, _85_202, _85_204) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _177_268 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _177_278 = (FStar_Syntax_Print.term_to_string t)
in Some (_177_278))
end else begin
None
end)


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (let _177_283 = (FStar_SMTEncoding_Term.mkFreeV ((xsym), (s)))
in ((xsym), (_177_283)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (let _177_288 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _177_288))
in (

let y = (FStar_SMTEncoding_Term.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let _85_218 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + 1); tcenv = _85_218.tcenv; warn = _85_218.warn; cache = _85_218.cache; nolabels = _85_218.nolabels; use_zfuel_name = _85_218.use_zfuel_name; encode_non_total_function_typ = _85_218.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Term.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let _85_224 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _85_224.depth; tcenv = _85_224.tcenv; warn = _85_224.warn; cache = _85_224.cache; nolabels = _85_224.nolabels; use_zfuel_name = _85_224.use_zfuel_name; encode_non_total_function_typ = _85_224.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let _85_229 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = _85_229.depth; tcenv = _85_229.tcenv; warn = _85_229.warn; cache = _85_229.cache; nolabels = _85_229.nolabels; use_zfuel_name = _85_229.use_zfuel_name; encode_non_total_function_typ = _85_229.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun _85_3 -> (match (_85_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some (((b), (t)))
end
| _85_241 -> begin
None
end))))
in (match ((aux a)) with
| None -> begin
(

let a = (unmangle a)
in (match ((aux a)) with
| None -> begin
(let _177_307 = (let _177_306 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found (after unmangling): %s" _177_306))
in (FStar_All.failwith _177_307))
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
in (let _177_318 = (

let _85_257 = env
in (let _177_317 = (let _177_316 = (let _177_315 = (let _177_314 = (let _177_313 = (FStar_SMTEncoding_Term.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _177_312 -> Some (_177_312)) _177_313))
in ((x), (fname), (_177_314), (None)))
in Binding_fvar (_177_315))
in (_177_316)::env.bindings)
in {bindings = _177_317; depth = _85_257.depth; tcenv = _85_257.tcenv; warn = _85_257.warn; cache = _85_257.cache; nolabels = _85_257.nolabels; use_zfuel_name = _85_257.use_zfuel_name; encode_non_total_function_typ = _85_257.encode_non_total_function_typ}))
in ((fname), (ftok), (_177_318))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _85_4 -> (match (_85_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| _85_269 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _177_329 = (lookup_binding env (fun _85_5 -> (match (_85_5) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| _85_280 -> begin
None
end)))
in (FStar_All.pipe_right _177_329 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _177_335 = (let _177_334 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _177_334))
in (FStar_All.failwith _177_335))
end
| Some (s) -> begin
s
end))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let _85_290 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = _85_290.depth; tcenv = _85_290.tcenv; warn = _85_290.warn; cache = _85_290.cache; nolabels = _85_290.nolabels; use_zfuel_name = _85_290.use_zfuel_name; encode_non_total_function_typ = _85_290.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let _85_299 = (lookup_lid env x)
in (match (_85_299) with
| (t1, t2, _85_298) -> begin
(

let t3 = (let _177_352 = (let _177_351 = (let _177_350 = (FStar_SMTEncoding_Term.mkApp (("ZFuel"), ([])))
in (_177_350)::[])
in ((f), (_177_351)))
in (FStar_SMTEncoding_Term.mkApp _177_352))
in (

let _85_301 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = _85_301.depth; tcenv = _85_301.tcenv; warn = _85_301.warn; cache = _85_301.cache; nolabels = _85_301.nolabels; use_zfuel_name = _85_301.use_zfuel_name; encode_non_total_function_typ = _85_301.encode_non_total_function_typ}))
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
| _85_314 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_85_318, (fuel)::[]) -> begin
if (let _177_358 = (let _177_357 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _177_357 Prims.fst))
in (FStar_Util.starts_with _177_358 "fuel")) then begin
(let _177_361 = (let _177_360 = (FStar_SMTEncoding_Term.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF _177_360 fuel))
in (FStar_All.pipe_left (fun _177_359 -> Some (_177_359)) _177_361))
end else begin
Some (t)
end
end
| _85_324 -> begin
Some (t)
end)
end
| _85_326 -> begin
None
end)
end)
end))


let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _177_365 = (let _177_364 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _177_364))
in (FStar_All.failwith _177_365))
end))


let lookup_free_var_name = (fun env a -> (

let _85_339 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_85_339) with
| (x, _85_336, _85_338) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let _85_345 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_85_345) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _85_349; FStar_SMTEncoding_Term.freevars = _85_347}) when env.use_zfuel_name -> begin
((g), (zf))
end
| _85_357 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| _85_367 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _85_6 -> (match (_85_6) with
| Binding_fvar (_85_372, nm', tok, _85_376) when (nm = nm') -> begin
tok
end
| _85_380 -> begin
None
end))))


let mkForall_fuel' = (fun n _85_385 -> (match (_85_385) with
| (pats, vars, body) -> begin
(

let fallback = (fun _85_387 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall ((pats), (vars), (body)))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(

let _85_390 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_390) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| _85_400 -> begin
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
(let _177_382 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _177_382))
end
| _85_413 -> begin
(let _177_383 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _177_383 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp ((guard), (body'))))
end
| _85_416 -> begin
body
end)
in (

let vars = (((fsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars
in (FStar_SMTEncoding_Term.mkForall ((pats), (vars), (body)))))))
end))
end)
end))


let mkForall_fuel : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' 1)


let head_normal : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_fvar (fv)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _177_389 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _177_389 FStar_Option.isNone))
end
| _85_455 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _177_394 = (FStar_Syntax_Util.un_uinst t)
in _177_394.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_85_459) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _177_395 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _177_395 FStar_Option.isSome))
end
| _85_464 -> begin
false
end))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _177_408 = (let _177_406 = (FStar_Syntax_Syntax.null_binder t)
in (_177_406)::[])
in (let _177_407 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _177_408 _177_407 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _177_415 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _177_415))
end
| s -> begin
(

let _85_476 = ()
in (let _177_416 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _177_416)))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _85_7 -> (match (_85_7) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _85_486 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _85_497; FStar_SMTEncoding_Term.freevars = _85_495})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _85_515) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _85_522 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_85_524, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _85_530 -> begin
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


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _85_8 -> (match (_85_8) with
| FStar_Const.Const_unit -> begin
FStar_SMTEncoding_Term.mk_Term_unit
end
| FStar_Const.Const_bool (true) -> begin
(FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
end
| FStar_Const.Const_bool (false) -> begin
(FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkFalse)
end
| FStar_Const.Const_char (c) -> begin
(let _177_473 = (let _177_472 = (let _177_471 = (let _177_470 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _177_470))
in (_177_471)::[])
in (("FStar.Char.Char"), (_177_472)))
in (FStar_SMTEncoding_Term.mkApp _177_473))
end
| FStar_Const.Const_int (i, None) -> begin
(let _177_474 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _177_474))
end
| FStar_Const.Const_int (i, Some (_85_550)) -> begin
(FStar_All.failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, _85_556) -> begin
(let _177_475 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _177_475))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _177_477 = (let _177_476 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _177_476))
in (FStar_All.failwith _177_477))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_85_570) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_85_573) -> begin
(let _177_486 = (FStar_Syntax_Util.unrefine t)
in (aux true _177_486))
end
| _85_576 -> begin
if norm then begin
(let _177_487 = (whnf env t)
in (aux false _177_487))
end else begin
(let _177_490 = (let _177_489 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _177_488 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _177_489 _177_488)))
in (FStar_All.failwith _177_490))
end
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _85_584 -> begin
(let _177_493 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_177_493)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (

let _85_588 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _177_541 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _177_541))
end else begin
()
end
in (

let _85_616 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _85_595 b -> (match (_85_595) with
| (vars, guards, env, decls, names) -> begin
(

let _85_610 = (

let x = (unmangle (Prims.fst b))
in (

let _85_601 = (gen_term_var env x)
in (match (_85_601) with
| (xxsym, xx, env') -> begin
(

let _85_604 = (let _177_544 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _177_544 env xx))
in (match (_85_604) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (_85_610) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (_85_616) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _85_623 = (encode_term t env)
in (match (_85_623) with
| (t, decls) -> begin
(let _177_549 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_177_549), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let _85_630 = (encode_term t env)
in (match (_85_630) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _177_554 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((_177_554), (decls)))
end
| Some (f) -> begin
(let _177_555 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((_177_555), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in (

let _85_637 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _177_560 = (FStar_Syntax_Print.tag_of_term t)
in (let _177_559 = (FStar_Syntax_Print.tag_of_term t0)
in (let _177_558 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _177_560 _177_559 _177_558))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _177_565 = (let _177_564 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _177_563 = (FStar_Syntax_Print.tag_of_term t0)
in (let _177_562 = (FStar_Syntax_Print.term_to_string t0)
in (let _177_561 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _177_564 _177_563 _177_562 _177_561)))))
in (FStar_All.failwith _177_565))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _177_567 = (let _177_566 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _177_566))
in (FStar_All.failwith _177_567))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _85_648) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _85_653) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _177_568 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((_177_568), ([])))
end
| FStar_Syntax_Syntax.Tm_type (_85_662) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, _85_666) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _177_569 = (encode_const c)
in ((_177_569), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _85_677 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_85_677) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(

let _85_684 = (encode_binders None binders env)
in (match (_85_684) with
| (vars, guards, env', decls, _85_683) -> begin
(

let fsym = (let _177_570 = (varops.fresh "f")
in ((_177_570), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let _85_692 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let _85_688 = env.tcenv
in {FStar_TypeChecker_Env.solver = _85_688.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _85_688.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _85_688.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _85_688.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _85_688.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _85_688.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _85_688.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _85_688.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _85_688.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _85_688.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _85_688.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _85_688.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _85_688.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _85_688.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _85_688.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _85_688.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _85_688.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _85_688.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _85_688.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _85_688.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _85_688.FStar_TypeChecker_Env.use_bv_sorts}) res)
in (match (_85_692) with
| (pre_opt, res_t) -> begin
(

let _85_695 = (encode_term_pred None res_t env' app)
in (match (_85_695) with
| (res_pred, decls') -> begin
(

let _85_704 = (match (pre_opt) with
| None -> begin
(let _177_571 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_177_571), ([])))
end
| Some (pre) -> begin
(

let _85_701 = (encode_formula pre env')
in (match (_85_701) with
| (guard, decls0) -> begin
(let _177_572 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in ((_177_572), (decls0)))
end))
end)
in (match (_85_704) with
| (guards, guard_decls) -> begin
(

let t_interp = (let _177_574 = (let _177_573 = (FStar_SMTEncoding_Term.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_177_573)))
in (FStar_SMTEncoding_Term.mkForall _177_574))
in (

let cvars = (let _177_576 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _177_576 (FStar_List.filter (fun _85_709 -> (match (_85_709) with
| (x, _85_708) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _85_715) -> begin
(let _177_579 = (let _177_578 = (let _177_577 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((t'), (_177_577)))
in (FStar_SMTEncoding_Term.mkApp _177_578))
in ((_177_579), ([])))
end
| None -> begin
(

let tsym = (varops.fresh "Tm_arrow")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = if (FStar_Options.log_queries ()) then begin
(let _177_580 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_177_580))
end else begin
None
end
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (let _177_582 = (let _177_581 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((tsym), (_177_581)))
in (FStar_SMTEncoding_Term.mkApp _177_582))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (let _177_584 = (let _177_583 = (FStar_SMTEncoding_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_177_583), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_584)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _177_591 = (let _177_590 = (let _177_589 = (let _177_588 = (let _177_587 = (let _177_586 = (let _177_585 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _177_585))
in ((f_has_t), (_177_586)))
in (FStar_SMTEncoding_Term.mkImp _177_587))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_177_588)))
in (mkForall_fuel _177_589))
in ((_177_590), (Some ("pre-typing for functions")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_591)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (let _177_595 = (let _177_594 = (let _177_593 = (let _177_592 = (FStar_SMTEncoding_Term.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_177_592)))
in (FStar_SMTEncoding_Term.mkForall _177_593))
in ((_177_594), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_595)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp)::[]))))
in (

let _85_734 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))))))
end))))
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

let t = (FStar_SMTEncoding_Term.mkApp ((tsym), ([])))
in (

let t_kinding = (

let a_name = Some ((Prims.strcat "non_total_function_typing_" tsym))
in (let _177_597 = (let _177_596 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((_177_596), (Some ("Typing for non-total arrows")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_597)))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _177_604 = (let _177_603 = (let _177_602 = (let _177_601 = (let _177_600 = (let _177_599 = (let _177_598 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _177_598))
in ((f_has_t), (_177_599)))
in (FStar_SMTEncoding_Term.mkImp _177_600))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_177_601)))
in (mkForall_fuel _177_602))
in ((_177_603), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_604)))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_85_747) -> begin
(

let _85_767 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _85_754; FStar_Syntax_Syntax.pos = _85_752; FStar_Syntax_Syntax.vars = _85_750} -> begin
(

let _85_762 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_85_762) with
| (b, f) -> begin
(let _177_606 = (let _177_605 = (FStar_List.hd b)
in (Prims.fst _177_605))
in ((_177_606), (f)))
end))
end
| _85_764 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_85_767) with
| (x, f) -> begin
(

let _85_770 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_85_770) with
| (base_t, decls) -> begin
(

let _85_774 = (gen_term_var env x)
in (match (_85_774) with
| (x, xtm, env') -> begin
(

let _85_777 = (encode_formula f env')
in (match (_85_777) with
| (refinement, decls') -> begin
(

let _85_780 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_780) with
| (fsym, fterm) -> begin
(

let encoding = (let _177_608 = (let _177_607 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_177_607), (refinement)))
in (FStar_SMTEncoding_Term.mkAnd _177_608))
in (

let cvars = (let _177_610 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _177_610 (FStar_List.filter (fun _85_785 -> (match (_85_785) with
| (y, _85_784) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = ((x), (FStar_SMTEncoding_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_SMTEncoding_Term.Fuel_sort))
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), ((ffv)::(xfv)::cvars), (encoding)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _85_792, _85_794) -> begin
(let _177_613 = (let _177_612 = (let _177_611 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((t), (_177_611)))
in (FStar_SMTEncoding_Term.mkApp _177_612))
in ((_177_613), ([])))
end
| None -> begin
(

let tsym = (varops.fresh "Tm_refine")
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (let _177_615 = (let _177_614 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((tsym), (_177_614)))
in (FStar_SMTEncoding_Term.mkApp _177_615))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t)
in (

let t_haseq = (let _177_619 = (let _177_618 = (let _177_617 = (let _177_616 = (FStar_SMTEncoding_Term.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (_177_616)))
in (FStar_SMTEncoding_Term.mkForall _177_617))
in ((_177_618), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym)))))
in FStar_SMTEncoding_Term.Assume (_177_619))
in (

let t_kinding = (let _177_621 = (let _177_620 = (FStar_SMTEncoding_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_177_620), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym)))))
in FStar_SMTEncoding_Term.Assume (_177_621))
in (

let t_interp = (let _177_627 = (let _177_626 = (let _177_623 = (let _177_622 = (FStar_SMTEncoding_Term.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_177_622)))
in (FStar_SMTEncoding_Term.mkForall _177_623))
in (let _177_625 = (let _177_624 = (FStar_Syntax_Print.term_to_string t0)
in Some (_177_624))
in ((_177_626), (_177_625), (Some ((Prims.strcat "refinement_interpretation_" tsym))))))
in FStar_SMTEncoding_Term.Assume (_177_627))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq)::[])))
in (

let _85_810 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(

let ttm = (let _177_628 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _177_628))
in (

let _85_819 = (encode_term_pred None k env ttm)
in (match (_85_819) with
| (t_has_k, decls) -> begin
(

let d = (let _177_634 = (let _177_633 = (let _177_632 = (let _177_631 = (let _177_630 = (let _177_629 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _177_629))
in (FStar_Util.format1 "@uvar_typing_%s" _177_630))
in (varops.fresh _177_631))
in Some (_177_632))
in ((t_has_k), (Some ("Uvar typing")), (_177_633)))
in FStar_SMTEncoding_Term.Assume (_177_634))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_85_822) -> begin
(

let _85_826 = (FStar_Syntax_Util.head_and_args t0)
in (match (_85_826) with
| (head, args_e) -> begin
(match ((let _177_636 = (let _177_635 = (FStar_Syntax_Subst.compress head)
in _177_635.FStar_Syntax_Syntax.n)
in ((_177_636), (args_e)))) with
| (_85_828, _85_830) when (head_redex env head) -> begin
(let _177_637 = (whnf env t)
in (encode_term _177_637 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let _85_870 = (encode_term v1 env)
in (match (_85_870) with
| (v1, decls1) -> begin
(

let _85_873 = (encode_term v2 env)
in (match (_85_873) with
| (v2, decls2) -> begin
(let _177_638 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in ((_177_638), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), (_85_882)::(_85_879)::_85_877) -> begin
(

let e0 = (let _177_642 = (let _177_641 = (let _177_640 = (let _177_639 = (FStar_List.hd args_e)
in (_177_639)::[])
in ((head), (_177_640)))
in FStar_Syntax_Syntax.Tm_app (_177_641))
in (FStar_Syntax_Syntax.mk _177_642 None head.FStar_Syntax_Syntax.pos))
in (

let e = (let _177_645 = (let _177_644 = (let _177_643 = (FStar_List.tl args_e)
in ((e0), (_177_643)))
in FStar_Syntax_Syntax.Tm_app (_177_644))
in (FStar_Syntax_Syntax.mk _177_645 None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env)))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), ((arg, _85_891))::[]) -> begin
(

let _85_897 = (encode_term arg env)
in (match (_85_897) with
| (tm, decls) -> begin
(let _177_646 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Var ("Reify")), ((tm)::[])))))
in ((_177_646), (decls)))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_85_899)), ((arg, _85_904))::[]) -> begin
(encode_term arg env)
end
| _85_909 -> begin
(

let _85_912 = (encode_args args_e env)
in (match (_85_912) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let _85_917 = (encode_term head env)
in (match (_85_917) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let _85_926 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_85_926) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun _85_930 _85_934 -> (match (((_85_930), (_85_934))) with
| ((bv, _85_929), (a, _85_933)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (let _177_651 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _177_651 (FStar_Syntax_Subst.subst subst)))
in (

let _85_939 = (encode_term_pred None ty env app_tm)
in (match (_85_939) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (let _177_655 = (let _177_654 = (FStar_SMTEncoding_Term.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (let _177_653 = (let _177_652 = (varops.fresh "@partial_app_typing_")
in Some (_177_652))
in ((_177_654), (Some ("Partial app typing")), (_177_653))))
in FStar_SMTEncoding_Term.Assume (_177_655))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let _85_946 = (lookup_free_var_sym env fv)
in (match (_85_946) with
| (fname, fuel_args) -> begin
(

let tm = (FStar_SMTEncoding_Term.mkApp' ((fname), ((FStar_List.append fuel_args args))))
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
(let _177_659 = (let _177_658 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _177_658 Prims.snd))
in Some (_177_659))
end
| FStar_Syntax_Syntax.Tm_ascribed (_85_978, FStar_Util.Inl (t), _85_982) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_85_986, FStar_Util.Inr (c), _85_990) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _85_994 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (let _177_660 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _177_660))
in (

let _85_1002 = (curried_arrow_formals_comp head_type)
in (match (_85_1002) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _85_1018 -> begin
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

let _85_1027 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_85_1027) with
| (bs, body, opening) -> begin
(

let fallback = (fun _85_1029 -> (match (()) with
| () -> begin
(

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (let _177_663 = (FStar_SMTEncoding_Term.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((_177_663), ((decl)::[])))))
end))
in (

let is_impure = (fun _85_9 -> (match (_85_9) with
| FStar_Util.Inl (lc) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)))
end
| FStar_Util.Inr (eff) -> begin
(let _177_666 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right _177_666 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _177_671 = (let _177_669 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _177_669))
in (FStar_All.pipe_right _177_671 (fun _177_670 -> Some (_177_670))))
end
| FStar_Util.Inr (eff) -> begin
(

let new_uvar = (fun _85_1045 -> (match (()) with
| () -> begin
(let _177_674 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _177_674 Prims.fst))
end))
in if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) then begin
(let _177_677 = (let _177_675 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total _177_675))
in (FStar_All.pipe_right _177_677 (fun _177_676 -> Some (_177_676))))
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) then begin
(let _177_680 = (let _177_678 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal _177_678))
in (FStar_All.pipe_right _177_680 (fun _177_679 -> Some (_177_679))))
end else begin
None
end
end)
end))
in (match (lopt) with
| None -> begin
(

let _85_1047 = (let _177_682 = (let _177_681 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _177_681))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _177_682))
in (fallback ()))
end
| Some (lc) -> begin
if (is_impure lc) then begin
(fallback ())
end else begin
(

let _85_1057 = (encode_binders None bs env)
in (match (_85_1057) with
| (vars, guards, envbody, decls, _85_1056) -> begin
(

let _85_1060 = (encode_term body envbody)
in (match (_85_1060) with
| (body, decls') -> begin
(

let key_body = (let _177_686 = (let _177_685 = (let _177_684 = (let _177_683 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_177_683), (body)))
in (FStar_SMTEncoding_Term.mkImp _177_684))
in (([]), (vars), (_177_685)))
in (FStar_SMTEncoding_Term.mkForall _177_686))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Term.mkForall (([]), (cvars), (key_body)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _85_1066, _85_1068) -> begin
(let _177_689 = (let _177_688 = (let _177_687 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((t), (_177_687)))
in (FStar_SMTEncoding_Term.mkApp _177_688))
in ((_177_689), ([])))
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

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (let _177_691 = (let _177_690 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((fsym), (_177_690)))
in (FStar_SMTEncoding_Term.mkApp _177_691))
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

let _85_1086 = (encode_term_pred None tfun env f)
in (match (_85_1086) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _177_695 = (let _177_694 = (let _177_693 = (let _177_692 = (FStar_SMTEncoding_Term.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_177_692), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_693))
in (_177_694)::[])
in (FStar_List.append decls'' _177_695)))
end)))
end)
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (let _177_699 = (let _177_698 = (let _177_697 = (let _177_696 = (FStar_SMTEncoding_Term.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_177_696)))
in (FStar_SMTEncoding_Term.mkForall _177_697))
in ((_177_698), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_177_699)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[]))))
in (

let _85_1092 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((fsym), (cvar_sorts), (f_decls)))
in ((f), (f_decls)))))))))))
end)
end))))
end))
end))
end
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_85_1095, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_85_1107); FStar_Syntax_Syntax.lbunivs = _85_1105; FStar_Syntax_Syntax.lbtyp = _85_1103; FStar_Syntax_Syntax.lbeff = _85_1101; FStar_Syntax_Syntax.lbdef = _85_1099})::_85_1097), _85_1113) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _85_1122; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _85_1119; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_85_1132) -> begin
(

let _85_1134 = (FStar_TypeChecker_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (let _177_700 = (FStar_SMTEncoding_Term.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((_177_700), ((decl_e)::[]))))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let _85_1150 = (encode_term e1 env)
in (match (_85_1150) with
| (ee1, decls1) -> begin
(

let _85_1153 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (_85_1153) with
| (xs, e2) -> begin
(

let _85_1157 = (FStar_List.hd xs)
in (match (_85_1157) with
| (x, _85_1156) -> begin
(

let env' = (push_term_var env x ee1)
in (

let _85_1161 = (encode_body e2 env')
in (match (_85_1161) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let _85_1169 = (encode_term e env)
in (match (_85_1169) with
| (scr, decls) -> begin
(

let _85_1206 = (FStar_List.fold_right (fun b _85_1173 -> (match (_85_1173) with
| (else_case, decls) -> begin
(

let _85_1177 = (FStar_Syntax_Subst.open_branch b)
in (match (_85_1177) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _85_1181 _85_1184 -> (match (((_85_1181), (_85_1184))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _85_1190 -> (match (_85_1190) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let _85_1200 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let _85_1197 = (encode_term w env)
in (match (_85_1197) with
| (w, decls2) -> begin
(let _177_734 = (let _177_733 = (let _177_732 = (let _177_731 = (let _177_730 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in ((w), (_177_730)))
in (FStar_SMTEncoding_Term.mkEq _177_731))
in ((guard), (_177_732)))
in (FStar_SMTEncoding_Term.mkAnd _177_733))
in ((_177_734), (decls2)))
end))
end)
in (match (_85_1200) with
| (guard, decls2) -> begin
(

let _85_1203 = (encode_br br env)
in (match (_85_1203) with
| (br, decls3) -> begin
(let _177_735 = (FStar_SMTEncoding_Term.mkITE ((guard), (br), (else_case)))
in ((_177_735), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (_85_1206) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _85_1212 -> begin
(let _177_738 = (encode_one_pat env pat)
in (_177_738)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (

let _85_1215 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _177_741 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _177_741))
end else begin
()
end
in (

let _85_1219 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_85_1219) with
| (vars, pat_term) -> begin
(

let _85_1231 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _85_1222 v -> (match (_85_1222) with
| (env, vars) -> begin
(

let _85_1228 = (gen_term_var env v)
in (match (_85_1228) with
| (xx, _85_1226, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (_85_1231) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_85_1236) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _177_749 = (let _177_748 = (encode_const c)
in ((scrutinee), (_177_748)))
in (FStar_SMTEncoding_Term.mkEq _177_749))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _85_1258 -> (match (_85_1258) with
| (arg, _85_1257) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _177_752 = (FStar_SMTEncoding_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _177_752)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_85_1265) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_85_1275) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _177_760 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _85_1285 -> (match (_85_1285) with
| (arg, _85_1284) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _177_759 = (FStar_SMTEncoding_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _177_759)))
end))))
in (FStar_All.pipe_right _177_760 FStar_List.flatten))
end))
in (

let pat_term = (fun _85_1288 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let _85_1304 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _85_1294 _85_1298 -> (match (((_85_1294), (_85_1298))) with
| ((tms, decls), (t, _85_1297)) -> begin
(

let _85_1301 = (encode_term t env)
in (match (_85_1301) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (_85_1304) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let rec list_elements = (fun e -> (

let _85_1313 = (let _177_773 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _177_773))
in (match (_85_1313) with
| (head, args) -> begin
(match ((let _177_775 = (let _177_774 = (FStar_Syntax_Util.un_uinst head)
in _177_774.FStar_Syntax_Syntax.n)
in ((_177_775), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _85_1317) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_85_1330)::((hd, _85_1327))::((tl, _85_1323))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _177_776 = (list_elements tl)
in (hd)::_177_776)
end
| _85_1334 -> begin
(

let _85_1335 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (

let one_pat = (fun p -> (

let _85_1341 = (let _177_779 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _177_779 FStar_Syntax_Util.head_and_args))
in (match (_85_1341) with
| (head, args) -> begin
(match ((let _177_781 = (let _177_780 = (FStar_Syntax_Util.un_uinst head)
in _177_780.FStar_Syntax_Syntax.n)
in ((_177_781), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((_85_1349, _85_1351))::((e, _85_1346))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _85_1359))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| _85_1364 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let _85_1372 = (let _177_786 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _177_786 FStar_Syntax_Util.head_and_args))
in (match (_85_1372) with
| (head, args) -> begin
(match ((let _177_788 = (let _177_787 = (FStar_Syntax_Util.un_uinst head)
in _177_787.FStar_Syntax_Syntax.n)
in ((_177_788), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _85_1377))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _85_1382 -> begin
None
end)
end)))
in (match (elts) with
| (t)::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _177_791 = (list_elements e)
in (FStar_All.pipe_right _177_791 (FStar_List.map (fun branch -> (let _177_790 = (list_elements branch)
in (FStar_All.pipe_right _177_790 (FStar_List.map one_pat)))))))
end
| _85_1389 -> begin
(let _177_792 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_177_792)::[])
end)
end
| _85_1391 -> begin
(let _177_793 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_177_793)::[])
end))))
in (

let _85_1425 = (match ((let _177_794 = (FStar_Syntax_Subst.compress t)
in _177_794.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let _85_1398 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_85_1398) with
| (binders, c) -> begin
(

let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((pre, _85_1410))::((post, _85_1406))::((pats, _85_1402))::[] -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _177_795 = (lemma_pats pats')
in ((binders), (pre), (post), (_177_795))))
end
| _85_1418 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _85_1420 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_85_1425) with
| (binders, pre, post, patterns) -> begin
(

let _85_1432 = (encode_binders None binders env)
in (match (_85_1432) with
| (vars, guards, env, decls, _85_1431) -> begin
(

let _85_1445 = (let _177_799 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let _85_1442 = (let _177_798 = (FStar_All.pipe_right branch (FStar_List.map (fun _85_1437 -> (match (_85_1437) with
| (t, _85_1436) -> begin
(encode_term t (

let _85_1438 = env
in {bindings = _85_1438.bindings; depth = _85_1438.depth; tcenv = _85_1438.tcenv; warn = _85_1438.warn; cache = _85_1438.cache; nolabels = _85_1438.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _85_1438.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _177_798 FStar_List.unzip))
in (match (_85_1442) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _177_799 FStar_List.unzip))
in (match (_85_1445) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _177_802 = (let _177_801 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _177_801 e))
in (_177_802)::p))))
end
| _85_1455 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _177_808 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_177_808)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _177_810 = (let _177_809 = (FStar_SMTEncoding_Term.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_LexCons _177_809 tl))
in (aux _177_810 vars))
end
| _85_1467 -> begin
pats
end))
in (let _177_811 = (FStar_SMTEncoding_Term.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux _177_811 vars)))
end)
end)
in (

let env = (

let _85_1469 = env
in {bindings = _85_1469.bindings; depth = _85_1469.depth; tcenv = _85_1469.tcenv; warn = _85_1469.warn; cache = _85_1469.cache; nolabels = true; use_zfuel_name = _85_1469.use_zfuel_name; encode_non_total_function_typ = _85_1469.encode_non_total_function_typ})
in (

let _85_1474 = (let _177_812 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _177_812 env))
in (match (_85_1474) with
| (pre, decls'') -> begin
(

let _85_1477 = (let _177_813 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _177_813 env))
in (match (_85_1477) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (let _177_818 = (let _177_817 = (let _177_816 = (let _177_815 = (let _177_814 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in ((_177_814), (post)))
in (FStar_SMTEncoding_Term.mkImp _177_815))
in ((pats), (vars), (_177_816)))
in (FStar_SMTEncoding_Term.mkForall _177_817))
in ((_177_818), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _177_824 = (FStar_Syntax_Print.tag_of_term phi)
in (let _177_823 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _177_824 _177_823)))
end else begin
()
end)
in (

let enc = (fun f l -> (

let _85_1493 = (FStar_Util.fold_map (fun decls x -> (

let _85_1490 = (encode_term (Prims.fst x) env)
in (match (_85_1490) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (_85_1493) with
| (decls, args) -> begin
(let _177_840 = (f args)
in ((_177_840), (decls)))
end)))
in (

let const_op = (fun f _85_1496 -> ((f), ([])))
in (

let un_op = (fun f l -> (let _177_854 = (FStar_List.hd l)
in (FStar_All.pipe_left f _177_854)))
in (

let bin_op = (fun f _85_10 -> (match (_85_10) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| _85_1507 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let enc_prop_c = (fun f l -> (

let _85_1522 = (FStar_Util.fold_map (fun decls _85_1516 -> (match (_85_1516) with
| (t, _85_1515) -> begin
(

let _85_1519 = (encode_formula t env)
in (match (_85_1519) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (_85_1522) with
| (decls, phis) -> begin
(let _177_879 = (f phis)
in ((_177_879), (decls)))
end)))
in (

let eq_op = (fun _85_11 -> (match (_85_11) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (

let mk_imp = (fun _85_12 -> (match (_85_12) with
| ((lhs, _85_1543))::((rhs, _85_1539))::[] -> begin
(

let _85_1548 = (encode_formula rhs env)
in (match (_85_1548) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _85_1551) -> begin
((l1), (decls1))
end
| _85_1555 -> begin
(

let _85_1558 = (encode_formula lhs env)
in (match (_85_1558) with
| (l2, decls2) -> begin
(let _177_884 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)))
in ((_177_884), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| _85_1560 -> begin
(FStar_All.failwith "impossible")
end))
in (

let mk_ite = (fun _85_13 -> (match (_85_13) with
| ((guard, _85_1573))::((_then, _85_1569))::((_else, _85_1565))::[] -> begin
(

let _85_1578 = (encode_formula guard env)
in (match (_85_1578) with
| (g, decls1) -> begin
(

let _85_1581 = (encode_formula _then env)
in (match (_85_1581) with
| (t, decls2) -> begin
(

let _85_1584 = (encode_formula _else env)
in (match (_85_1584) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)))
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| _85_1587 -> begin
(FStar_All.failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (let _177_896 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _177_896)))
in (

let connectives = (let _177_952 = (let _177_905 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in ((FStar_Syntax_Const.and_lid), (_177_905)))
in (let _177_951 = (let _177_950 = (let _177_911 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in ((FStar_Syntax_Const.or_lid), (_177_911)))
in (let _177_949 = (let _177_948 = (let _177_947 = (let _177_920 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in ((FStar_Syntax_Const.iff_lid), (_177_920)))
in (let _177_946 = (let _177_945 = (let _177_944 = (let _177_929 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in ((FStar_Syntax_Const.not_lid), (_177_929)))
in (_177_944)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::_177_945)
in (_177_947)::_177_946))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::_177_948)
in (_177_950)::_177_949))
in (_177_952)::_177_951))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let _85_1605 = (encode_formula phi' env)
in (match (_85_1605) with
| (phi, decls) -> begin
(let _177_955 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))))
in ((_177_955), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (_85_1607) -> begin
(let _177_956 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula _177_956 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let _85_1615 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_85_1615) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _85_1622; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _85_1619; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let _85_1633 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_85_1633) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_85_1650)::((x, _85_1647))::((t, _85_1643))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let _85_1655 = (encode_term x env)
in (match (_85_1655) with
| (x, decls) -> begin
(

let _85_1658 = (encode_term t env)
in (match (_85_1658) with
| (t, decls') -> begin
(let _177_957 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((_177_957), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, _85_1671))::((msg, _85_1667))::((phi, _85_1663))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _177_961 = (let _177_958 = (FStar_Syntax_Subst.compress r)
in _177_958.FStar_Syntax_Syntax.n)
in (let _177_960 = (let _177_959 = (FStar_Syntax_Subst.compress msg)
in _177_959.FStar_Syntax_Syntax.n)
in ((_177_961), (_177_960))))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _85_1680))) -> begin
(

let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false))))))) None r)
in (fallback phi))
end
| _85_1687 -> begin
(fallback phi)
end)
end
| _85_1689 when (head_redex env head) -> begin
(let _177_962 = (whnf env phi)
in (encode_formula _177_962 env))
end
| _85_1691 -> begin
(

let _85_1694 = (encode_term phi env)
in (match (_85_1694) with
| (tt, decls) -> begin
(let _177_963 = (FStar_SMTEncoding_Term.mk_Valid tt)
in ((_177_963), (decls)))
end))
end))
end
| _85_1696 -> begin
(

let _85_1699 = (encode_term phi env)
in (match (_85_1699) with
| (tt, decls) -> begin
(let _177_964 = (FStar_SMTEncoding_Term.mk_Valid tt)
in ((_177_964), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let _85_1711 = (encode_binders None bs env)
in (match (_85_1711) with
| (vars, guards, env, decls, _85_1710) -> begin
(

let _85_1724 = (let _177_976 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let _85_1721 = (let _177_975 = (FStar_All.pipe_right p (FStar_List.map (fun _85_1716 -> (match (_85_1716) with
| (t, _85_1715) -> begin
(encode_term t (

let _85_1717 = env
in {bindings = _85_1717.bindings; depth = _85_1717.depth; tcenv = _85_1717.tcenv; warn = _85_1717.warn; cache = _85_1717.cache; nolabels = _85_1717.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _85_1717.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _177_975 FStar_List.unzip))
in (match (_85_1721) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _177_976 FStar_List.unzip))
in (match (_85_1724) with
| (pats, decls') -> begin
(

let _85_1727 = (encode_formula body env)
in (match (_85_1727) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.hash = _85_1731; FStar_SMTEncoding_Term.freevars = _85_1729})::[])::[] -> begin
[]
end
| _85_1742 -> begin
guards
end)
in (let _177_977 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((vars), (pats), (_177_977), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in (

let _85_1744 = (debug phi)
in (

let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _85_1756 -> (match (_85_1756) with
| (l, _85_1755) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_85_1759, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(

let _85_1769 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _177_994 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _177_994))
end else begin
()
end
in (

let _85_1776 = (encode_q_body env vars pats body)
in (match (_85_1776) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (let _177_996 = (let _177_995 = (FStar_SMTEncoding_Term.mkImp ((guard), (body)))
in ((pats), (vars), (_177_995)))
in (FStar_SMTEncoding_Term.mkForall _177_996))
in (

let _85_1778 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _177_997 = (FStar_SMTEncoding_Term.termToSmt tm)
in (FStar_Util.print1 ">>>> Encoded QALL to %s\n" _177_997))
end else begin
()
end
in ((tm), (decls))))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(

let _85_1791 = (encode_q_body env vars pats body)
in (match (_85_1791) with
| (vars, pats, guard, body, decls) -> begin
(let _177_1000 = (let _177_999 = (let _177_998 = (FStar_SMTEncoding_Term.mkAnd ((guard), (body)))
in ((pats), (vars), (_177_998)))
in (FStar_SMTEncoding_Term.mkExists _177_999))
in ((_177_1000), (decls)))
end))
end)))))))))))))))))


type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}


let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))


let prims : prims_t = (

let _85_1797 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_1797) with
| (asym, a) -> begin
(

let _85_1800 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_1800) with
| (xsym, x) -> begin
(

let _85_1803 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_1803) with
| (ysym, y) -> begin
(

let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun (((x), (vars), (FStar_SMTEncoding_Term.Term_sort), (body), (None))))::[])
in (

let quant = (fun vars body x -> (

let t1 = (let _177_1043 = (let _177_1042 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((x), (_177_1042)))
in (FStar_SMTEncoding_Term.mkApp _177_1043))
in (

let vname_decl = (let _177_1045 = (let _177_1044 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_177_1044), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_177_1045))
in (let _177_1051 = (let _177_1050 = (let _177_1049 = (let _177_1048 = (let _177_1047 = (let _177_1046 = (FStar_SMTEncoding_Term.mkEq ((t1), (body)))
in ((((t1)::[])::[]), (vars), (_177_1046)))
in (FStar_SMTEncoding_Term.mkForall _177_1047))
in ((_177_1048), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (_177_1049))
in (_177_1050)::[])
in (vname_decl)::_177_1051))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (let _177_1211 = (let _177_1060 = (let _177_1059 = (let _177_1058 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1058))
in (quant axy _177_1059))
in ((FStar_Syntax_Const.op_Eq), (_177_1060)))
in (let _177_1210 = (let _177_1209 = (let _177_1067 = (let _177_1066 = (let _177_1065 = (let _177_1064 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in (FStar_SMTEncoding_Term.mkNot _177_1064))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1065))
in (quant axy _177_1066))
in ((FStar_Syntax_Const.op_notEq), (_177_1067)))
in (let _177_1208 = (let _177_1207 = (let _177_1076 = (let _177_1075 = (let _177_1074 = (let _177_1073 = (let _177_1072 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1071 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1072), (_177_1071))))
in (FStar_SMTEncoding_Term.mkLT _177_1073))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1074))
in (quant xy _177_1075))
in ((FStar_Syntax_Const.op_LT), (_177_1076)))
in (let _177_1206 = (let _177_1205 = (let _177_1085 = (let _177_1084 = (let _177_1083 = (let _177_1082 = (let _177_1081 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1080 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1081), (_177_1080))))
in (FStar_SMTEncoding_Term.mkLTE _177_1082))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1083))
in (quant xy _177_1084))
in ((FStar_Syntax_Const.op_LTE), (_177_1085)))
in (let _177_1204 = (let _177_1203 = (let _177_1094 = (let _177_1093 = (let _177_1092 = (let _177_1091 = (let _177_1090 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1089 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1090), (_177_1089))))
in (FStar_SMTEncoding_Term.mkGT _177_1091))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1092))
in (quant xy _177_1093))
in ((FStar_Syntax_Const.op_GT), (_177_1094)))
in (let _177_1202 = (let _177_1201 = (let _177_1103 = (let _177_1102 = (let _177_1101 = (let _177_1100 = (let _177_1099 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1098 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1099), (_177_1098))))
in (FStar_SMTEncoding_Term.mkGTE _177_1100))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1101))
in (quant xy _177_1102))
in ((FStar_Syntax_Const.op_GTE), (_177_1103)))
in (let _177_1200 = (let _177_1199 = (let _177_1112 = (let _177_1111 = (let _177_1110 = (let _177_1109 = (let _177_1108 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1107 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1108), (_177_1107))))
in (FStar_SMTEncoding_Term.mkSub _177_1109))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1110))
in (quant xy _177_1111))
in ((FStar_Syntax_Const.op_Subtraction), (_177_1112)))
in (let _177_1198 = (let _177_1197 = (let _177_1119 = (let _177_1118 = (let _177_1117 = (let _177_1116 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _177_1116))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1117))
in (quant qx _177_1118))
in ((FStar_Syntax_Const.op_Minus), (_177_1119)))
in (let _177_1196 = (let _177_1195 = (let _177_1128 = (let _177_1127 = (let _177_1126 = (let _177_1125 = (let _177_1124 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1123 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1124), (_177_1123))))
in (FStar_SMTEncoding_Term.mkAdd _177_1125))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1126))
in (quant xy _177_1127))
in ((FStar_Syntax_Const.op_Addition), (_177_1128)))
in (let _177_1194 = (let _177_1193 = (let _177_1137 = (let _177_1136 = (let _177_1135 = (let _177_1134 = (let _177_1133 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1132 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1133), (_177_1132))))
in (FStar_SMTEncoding_Term.mkMul _177_1134))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1135))
in (quant xy _177_1136))
in ((FStar_Syntax_Const.op_Multiply), (_177_1137)))
in (let _177_1192 = (let _177_1191 = (let _177_1146 = (let _177_1145 = (let _177_1144 = (let _177_1143 = (let _177_1142 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1141 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1142), (_177_1141))))
in (FStar_SMTEncoding_Term.mkDiv _177_1143))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1144))
in (quant xy _177_1145))
in ((FStar_Syntax_Const.op_Division), (_177_1146)))
in (let _177_1190 = (let _177_1189 = (let _177_1155 = (let _177_1154 = (let _177_1153 = (let _177_1152 = (let _177_1151 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1150 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_177_1151), (_177_1150))))
in (FStar_SMTEncoding_Term.mkMod _177_1152))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _177_1153))
in (quant xy _177_1154))
in ((FStar_Syntax_Const.op_Modulus), (_177_1155)))
in (let _177_1188 = (let _177_1187 = (let _177_1164 = (let _177_1163 = (let _177_1162 = (let _177_1161 = (let _177_1160 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _177_1159 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_177_1160), (_177_1159))))
in (FStar_SMTEncoding_Term.mkAnd _177_1161))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1162))
in (quant xy _177_1163))
in ((FStar_Syntax_Const.op_And), (_177_1164)))
in (let _177_1186 = (let _177_1185 = (let _177_1173 = (let _177_1172 = (let _177_1171 = (let _177_1170 = (let _177_1169 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _177_1168 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_177_1169), (_177_1168))))
in (FStar_SMTEncoding_Term.mkOr _177_1170))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1171))
in (quant xy _177_1172))
in ((FStar_Syntax_Const.op_Or), (_177_1173)))
in (let _177_1184 = (let _177_1183 = (let _177_1180 = (let _177_1179 = (let _177_1178 = (let _177_1177 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _177_1177))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1178))
in (quant qx _177_1179))
in ((FStar_Syntax_Const.op_Negation), (_177_1180)))
in (_177_1183)::[])
in (_177_1185)::_177_1184))
in (_177_1187)::_177_1186))
in (_177_1189)::_177_1188))
in (_177_1191)::_177_1190))
in (_177_1193)::_177_1192))
in (_177_1195)::_177_1194))
in (_177_1197)::_177_1196))
in (_177_1199)::_177_1198))
in (_177_1201)::_177_1200))
in (_177_1203)::_177_1202))
in (_177_1205)::_177_1204))
in (_177_1207)::_177_1206))
in (_177_1209)::_177_1208))
in (_177_1211)::_177_1210))
in (

let mk = (fun l v -> (let _177_1243 = (FStar_All.pipe_right prims (FStar_List.filter (fun _85_1823 -> (match (_85_1823) with
| (l', _85_1822) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _177_1243 (FStar_List.collect (fun _85_1827 -> (match (_85_1827) with
| (_85_1825, b) -> begin
(b v)
end))))))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _85_1833 -> (match (_85_1833) with
| (l', _85_1832) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let _85_1839 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_1839) with
| (xxsym, xx) -> begin
(

let _85_1842 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_1842) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _177_1271 = (let _177_1270 = (let _177_1267 = (let _177_1266 = (let _177_1265 = (let _177_1264 = (let _177_1263 = (let _177_1262 = (FStar_SMTEncoding_Term.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_177_1262)))
in (FStar_SMTEncoding_Term.mkEq _177_1263))
in ((xx_has_type), (_177_1264)))
in (FStar_SMTEncoding_Term.mkImp _177_1265))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (_177_1266)))
in (FStar_SMTEncoding_Term.mkForall _177_1267))
in (let _177_1269 = (let _177_1268 = (varops.fresh "@pretyping_")
in Some (_177_1268))
in ((_177_1270), (Some ("pretyping")), (_177_1269))))
in FStar_SMTEncoding_Term.Assume (_177_1271)))
end))
end)))


let primitive_type_axioms : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (

let mk_unit = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _177_1292 = (let _177_1283 = (let _177_1282 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((_177_1282), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (_177_1283))
in (let _177_1291 = (let _177_1290 = (let _177_1289 = (let _177_1288 = (let _177_1287 = (let _177_1286 = (let _177_1285 = (let _177_1284 = (FStar_SMTEncoding_Term.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (_177_1284)))
in (FStar_SMTEncoding_Term.mkImp _177_1285))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_177_1286)))
in (mkForall_fuel _177_1287))
in ((_177_1288), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1289))
in (_177_1290)::[])
in (_177_1292)::_177_1291))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _177_1315 = (let _177_1306 = (let _177_1305 = (let _177_1304 = (let _177_1303 = (let _177_1300 = (let _177_1299 = (FStar_SMTEncoding_Term.boxBool b)
in (_177_1299)::[])
in (_177_1300)::[])
in (let _177_1302 = (let _177_1301 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _177_1301 tt))
in ((_177_1303), ((bb)::[]), (_177_1302))))
in (FStar_SMTEncoding_Term.mkForall _177_1304))
in ((_177_1305), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (_177_1306))
in (let _177_1314 = (let _177_1313 = (let _177_1312 = (let _177_1311 = (let _177_1310 = (let _177_1309 = (let _177_1308 = (let _177_1307 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_177_1307)))
in (FStar_SMTEncoding_Term.mkImp _177_1308))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_177_1309)))
in (mkForall_fuel _177_1310))
in ((_177_1311), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1312))
in (_177_1313)::[])
in (_177_1315)::_177_1314))))))
in (

let mk_int = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Int_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Int_sort))
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let precedes = (let _177_1329 = (let _177_1328 = (let _177_1327 = (let _177_1326 = (let _177_1325 = (let _177_1324 = (FStar_SMTEncoding_Term.boxInt a)
in (let _177_1323 = (let _177_1322 = (FStar_SMTEncoding_Term.boxInt b)
in (_177_1322)::[])
in (_177_1324)::_177_1323))
in (tt)::_177_1325)
in (tt)::_177_1326)
in (("Prims.Precedes"), (_177_1327)))
in (FStar_SMTEncoding_Term.mkApp _177_1328))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _177_1329))
in (

let precedes_y_x = (let _177_1330 = (FStar_SMTEncoding_Term.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _177_1330))
in (let _177_1372 = (let _177_1338 = (let _177_1337 = (let _177_1336 = (let _177_1335 = (let _177_1332 = (let _177_1331 = (FStar_SMTEncoding_Term.boxInt b)
in (_177_1331)::[])
in (_177_1332)::[])
in (let _177_1334 = (let _177_1333 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _177_1333 tt))
in ((_177_1335), ((bb)::[]), (_177_1334))))
in (FStar_SMTEncoding_Term.mkForall _177_1336))
in ((_177_1337), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (_177_1338))
in (let _177_1371 = (let _177_1370 = (let _177_1344 = (let _177_1343 = (let _177_1342 = (let _177_1341 = (let _177_1340 = (let _177_1339 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_177_1339)))
in (FStar_SMTEncoding_Term.mkImp _177_1340))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_177_1341)))
in (mkForall_fuel _177_1342))
in ((_177_1343), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1344))
in (let _177_1369 = (let _177_1368 = (let _177_1367 = (let _177_1366 = (let _177_1365 = (let _177_1364 = (let _177_1363 = (let _177_1362 = (let _177_1361 = (let _177_1360 = (let _177_1359 = (let _177_1358 = (let _177_1347 = (let _177_1346 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _177_1345 = (FStar_SMTEncoding_Term.mkInteger' 0)
in ((_177_1346), (_177_1345))))
in (FStar_SMTEncoding_Term.mkGT _177_1347))
in (let _177_1357 = (let _177_1356 = (let _177_1350 = (let _177_1349 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _177_1348 = (FStar_SMTEncoding_Term.mkInteger' 0)
in ((_177_1349), (_177_1348))))
in (FStar_SMTEncoding_Term.mkGTE _177_1350))
in (let _177_1355 = (let _177_1354 = (let _177_1353 = (let _177_1352 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _177_1351 = (FStar_SMTEncoding_Term.unboxInt x)
in ((_177_1352), (_177_1351))))
in (FStar_SMTEncoding_Term.mkLT _177_1353))
in (_177_1354)::[])
in (_177_1356)::_177_1355))
in (_177_1358)::_177_1357))
in (typing_pred_y)::_177_1359)
in (typing_pred)::_177_1360)
in (FStar_SMTEncoding_Term.mk_and_l _177_1361))
in ((_177_1362), (precedes_y_x)))
in (FStar_SMTEncoding_Term.mkImp _177_1363))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_177_1364)))
in (mkForall_fuel _177_1365))
in ((_177_1366), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (_177_1367))
in (_177_1368)::[])
in (_177_1370)::_177_1369))
in (_177_1372)::_177_1371)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _177_1395 = (let _177_1386 = (let _177_1385 = (let _177_1384 = (let _177_1383 = (let _177_1380 = (let _177_1379 = (FStar_SMTEncoding_Term.boxString b)
in (_177_1379)::[])
in (_177_1380)::[])
in (let _177_1382 = (let _177_1381 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _177_1381 tt))
in ((_177_1383), ((bb)::[]), (_177_1382))))
in (FStar_SMTEncoding_Term.mkForall _177_1384))
in ((_177_1385), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (_177_1386))
in (let _177_1394 = (let _177_1393 = (let _177_1392 = (let _177_1391 = (let _177_1390 = (let _177_1389 = (let _177_1388 = (let _177_1387 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (_177_1387)))
in (FStar_SMTEncoding_Term.mkImp _177_1388))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_177_1389)))
in (mkForall_fuel _177_1390))
in ((_177_1391), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1392))
in (_177_1393)::[])
in (_177_1395)::_177_1394))))))
in (

let mk_ref = (fun env reft_name _85_1881 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (let _177_1404 = (let _177_1403 = (let _177_1402 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_177_1402)::[])
in ((reft_name), (_177_1403)))
in (FStar_SMTEncoding_Term.mkApp _177_1404))
in (

let refb = (let _177_1407 = (let _177_1406 = (let _177_1405 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_177_1405)::[])
in ((reft_name), (_177_1406)))
in (FStar_SMTEncoding_Term.mkApp _177_1407))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _177_1426 = (let _177_1413 = (let _177_1412 = (let _177_1411 = (let _177_1410 = (let _177_1409 = (let _177_1408 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_177_1408)))
in (FStar_SMTEncoding_Term.mkImp _177_1409))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_177_1410)))
in (mkForall_fuel _177_1411))
in ((_177_1412), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (_177_1413))
in (let _177_1425 = (let _177_1424 = (let _177_1423 = (let _177_1422 = (let _177_1421 = (let _177_1420 = (let _177_1419 = (let _177_1418 = (FStar_SMTEncoding_Term.mkAnd ((typing_pred), (typing_pred_b)))
in (let _177_1417 = (let _177_1416 = (let _177_1415 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _177_1414 = (FStar_SMTEncoding_Term.mkFreeV bb)
in ((_177_1415), (_177_1414))))
in (FStar_SMTEncoding_Term.mkEq _177_1416))
in ((_177_1418), (_177_1417))))
in (FStar_SMTEncoding_Term.mkImp _177_1419))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_177_1420)))
in (mkForall_fuel' 2 _177_1421))
in ((_177_1422), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (_177_1423))
in (_177_1424)::[])
in (_177_1426)::_177_1425))))))))))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((false_tm)::[])))
in (let _177_1435 = (let _177_1434 = (let _177_1433 = (FStar_SMTEncoding_Term.mkIff ((FStar_SMTEncoding_Term.mkFalse), (valid)))
in ((_177_1433), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1434))
in (_177_1435)::[])))
in (

let mk_and_interp = (fun env conj _85_1898 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _177_1444 = (let _177_1443 = (let _177_1442 = (FStar_SMTEncoding_Term.mkApp ((conj), ((a)::(b)::[])))
in (_177_1442)::[])
in (("Valid"), (_177_1443)))
in (FStar_SMTEncoding_Term.mkApp _177_1444))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _177_1451 = (let _177_1450 = (let _177_1449 = (let _177_1448 = (let _177_1447 = (let _177_1446 = (let _177_1445 = (FStar_SMTEncoding_Term.mkAnd ((valid_a), (valid_b)))
in ((_177_1445), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1446))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1447)))
in (FStar_SMTEncoding_Term.mkForall _177_1448))
in ((_177_1449), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1450))
in (_177_1451)::[])))))))))
in (

let mk_or_interp = (fun env disj _85_1910 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _177_1460 = (let _177_1459 = (let _177_1458 = (FStar_SMTEncoding_Term.mkApp ((disj), ((a)::(b)::[])))
in (_177_1458)::[])
in (("Valid"), (_177_1459)))
in (FStar_SMTEncoding_Term.mkApp _177_1460))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _177_1467 = (let _177_1466 = (let _177_1465 = (let _177_1464 = (let _177_1463 = (let _177_1462 = (let _177_1461 = (FStar_SMTEncoding_Term.mkOr ((valid_a), (valid_b)))
in ((_177_1461), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1462))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1463)))
in (FStar_SMTEncoding_Term.mkForall _177_1464))
in ((_177_1465), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1466))
in (_177_1467)::[])))))))))
in (

let mk_eq2_interp = (fun env eq2 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (

let valid = (let _177_1476 = (let _177_1475 = (let _177_1474 = (FStar_SMTEncoding_Term.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (_177_1474)::[])
in (("Valid"), (_177_1475)))
in (FStar_SMTEncoding_Term.mkApp _177_1476))
in (let _177_1483 = (let _177_1482 = (let _177_1481 = (let _177_1480 = (let _177_1479 = (let _177_1478 = (let _177_1477 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in ((_177_1477), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1478))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (_177_1479)))
in (FStar_SMTEncoding_Term.mkForall _177_1480))
in ((_177_1481), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1482))
in (_177_1483)::[])))))))))
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

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (

let valid = (let _177_1492 = (let _177_1491 = (let _177_1490 = (FStar_SMTEncoding_Term.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (_177_1490)::[])
in (("Valid"), (_177_1491)))
in (FStar_SMTEncoding_Term.mkApp _177_1492))
in (let _177_1499 = (let _177_1498 = (let _177_1497 = (let _177_1496 = (let _177_1495 = (let _177_1494 = (let _177_1493 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in ((_177_1493), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1494))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_177_1495)))
in (FStar_SMTEncoding_Term.mkForall _177_1496))
in ((_177_1497), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1498))
in (_177_1499)::[])))))))))))
in (

let mk_imp_interp = (fun env imp tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _177_1508 = (let _177_1507 = (let _177_1506 = (FStar_SMTEncoding_Term.mkApp ((imp), ((a)::(b)::[])))
in (_177_1506)::[])
in (("Valid"), (_177_1507)))
in (FStar_SMTEncoding_Term.mkApp _177_1508))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _177_1515 = (let _177_1514 = (let _177_1513 = (let _177_1512 = (let _177_1511 = (let _177_1510 = (let _177_1509 = (FStar_SMTEncoding_Term.mkImp ((valid_a), (valid_b)))
in ((_177_1509), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1510))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1511)))
in (FStar_SMTEncoding_Term.mkForall _177_1512))
in ((_177_1513), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1514))
in (_177_1515)::[])))))))))
in (

let mk_iff_interp = (fun env iff tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let valid = (let _177_1524 = (let _177_1523 = (let _177_1522 = (FStar_SMTEncoding_Term.mkApp ((iff), ((a)::(b)::[])))
in (_177_1522)::[])
in (("Valid"), (_177_1523)))
in (FStar_SMTEncoding_Term.mkApp _177_1524))
in (

let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _177_1531 = (let _177_1530 = (let _177_1529 = (let _177_1528 = (let _177_1527 = (let _177_1526 = (let _177_1525 = (FStar_SMTEncoding_Term.mkIff ((valid_a), (valid_b)))
in ((_177_1525), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1526))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1527)))
in (FStar_SMTEncoding_Term.mkForall _177_1528))
in ((_177_1529), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1530))
in (_177_1531)::[])))))))))
in (

let mk_forall_interp = (fun env for_all tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let valid = (let _177_1540 = (let _177_1539 = (let _177_1538 = (FStar_SMTEncoding_Term.mkApp ((for_all), ((a)::(b)::[])))
in (_177_1538)::[])
in (("Valid"), (_177_1539)))
in (FStar_SMTEncoding_Term.mkApp _177_1540))
in (

let valid_b_x = (let _177_1543 = (let _177_1542 = (let _177_1541 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_177_1541)::[])
in (("Valid"), (_177_1542)))
in (FStar_SMTEncoding_Term.mkApp _177_1543))
in (let _177_1557 = (let _177_1556 = (let _177_1555 = (let _177_1554 = (let _177_1553 = (let _177_1552 = (let _177_1551 = (let _177_1550 = (let _177_1549 = (let _177_1545 = (let _177_1544 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_177_1544)::[])
in (_177_1545)::[])
in (let _177_1548 = (let _177_1547 = (let _177_1546 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_177_1546), (valid_b_x)))
in (FStar_SMTEncoding_Term.mkImp _177_1547))
in ((_177_1549), ((xx)::[]), (_177_1548))))
in (FStar_SMTEncoding_Term.mkForall _177_1550))
in ((_177_1551), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1552))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1553)))
in (FStar_SMTEncoding_Term.mkForall _177_1554))
in ((_177_1555), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1556))
in (_177_1557)::[]))))))))))
in (

let mk_exists_interp = (fun env for_some tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let valid = (let _177_1566 = (let _177_1565 = (let _177_1564 = (FStar_SMTEncoding_Term.mkApp ((for_some), ((a)::(b)::[])))
in (_177_1564)::[])
in (("Valid"), (_177_1565)))
in (FStar_SMTEncoding_Term.mkApp _177_1566))
in (

let valid_b_x = (let _177_1569 = (let _177_1568 = (let _177_1567 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_177_1567)::[])
in (("Valid"), (_177_1568)))
in (FStar_SMTEncoding_Term.mkApp _177_1569))
in (let _177_1583 = (let _177_1582 = (let _177_1581 = (let _177_1580 = (let _177_1579 = (let _177_1578 = (let _177_1577 = (let _177_1576 = (let _177_1575 = (let _177_1571 = (let _177_1570 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_177_1570)::[])
in (_177_1571)::[])
in (let _177_1574 = (let _177_1573 = (let _177_1572 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_177_1572), (valid_b_x)))
in (FStar_SMTEncoding_Term.mkImp _177_1573))
in ((_177_1575), ((xx)::[]), (_177_1574))))
in (FStar_SMTEncoding_Term.mkExists _177_1576))
in ((_177_1577), (valid)))
in (FStar_SMTEncoding_Term.mkIff _177_1578))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_177_1579)))
in (FStar_SMTEncoding_Term.mkForall _177_1580))
in ((_177_1581), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (_177_1582))
in (_177_1583)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Term.mkApp ((range), ([])))
in (let _177_1594 = (let _177_1593 = (let _177_1592 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _177_1591 = (let _177_1590 = (varops.fresh "typing_range_const")
in Some (_177_1590))
in ((_177_1592), (Some ("Range_const typing")), (_177_1591))))
in FStar_SMTEncoding_Term.Assume (_177_1593))
in (_177_1594)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _85_2003 -> (match (_85_2003) with
| (l, _85_2002) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_85_2006, f) -> begin
(f env s tt)
end))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _85_2016 = (encode_function_type_as_formula None None t env)
in (match (_85_2016) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _177_1793 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _177_1793)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(

let _85_2026 = (new_term_constant_and_tok_from_lid env lid)
in (match (_85_2026) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (match ((let _177_1794 = (FStar_Syntax_Subst.compress t_norm)
in _177_1794.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _85_2029) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _85_2032 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _85_2035 -> begin
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

let definition = (prims.mk lid vname)
in (

let env = (push_free_var env lid vname None)
in ((definition), (env)))))
end else begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let _85_2050 = (

let _85_2045 = (curried_arrow_formals_comp t_norm)
in (match (_85_2045) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _177_1796 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_177_1796)))
end else begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end
end))
in (match (_85_2050) with
| (formals, (pre_opt, res_t)) -> begin
(

let _85_2054 = (new_term_constant_and_tok_from_lid env lid)
in (match (_85_2054) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| _85_2057 -> begin
(FStar_SMTEncoding_Term.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _85_14 -> (match (_85_14) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let _85_2073 = (FStar_Util.prefix vars)
in (match (_85_2073) with
| (_85_2068, (xxsym, _85_2071)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (let _177_1813 = (let _177_1812 = (let _177_1811 = (let _177_1810 = (let _177_1809 = (let _177_1808 = (let _177_1807 = (let _177_1806 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _177_1806))
in ((vapp), (_177_1807)))
in (FStar_SMTEncoding_Term.mkEq _177_1808))
in ((((vapp)::[])::[]), (vars), (_177_1809)))
in (FStar_SMTEncoding_Term.mkForall _177_1810))
in ((_177_1811), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (_177_1812))
in (_177_1813)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let _85_2085 = (FStar_Util.prefix vars)
in (match (_85_2085) with
| (_85_2080, (xxsym, _85_2083)) -> begin
(

let xx = (FStar_SMTEncoding_Term.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Term.mkApp ((tp_name), ((xx)::[])))
in (let _177_1818 = (let _177_1817 = (let _177_1816 = (let _177_1815 = (let _177_1814 = (FStar_SMTEncoding_Term.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_177_1814)))
in (FStar_SMTEncoding_Term.mkForall _177_1815))
in ((_177_1816), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (_177_1817))
in (_177_1818)::[])))))
end))
end
| _85_2091 -> begin
[]
end)))))
in (

let _85_2098 = (encode_binders None formals env)
in (match (_85_2098) with
| (vars, guards, env', decls1, _85_2097) -> begin
(

let _85_2107 = (match (pre_opt) with
| None -> begin
(let _177_1819 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_177_1819), (decls1)))
end
| Some (p) -> begin
(

let _85_2104 = (encode_formula p env')
in (match (_85_2104) with
| (g, ds) -> begin
(let _177_1820 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in ((_177_1820), ((FStar_List.append decls1 ds))))
end))
end)
in (match (_85_2107) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (let _177_1822 = (let _177_1821 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((vname), (_177_1821)))
in (FStar_SMTEncoding_Term.mkApp _177_1822))
in (

let _85_2131 = (

let vname_decl = (let _177_1825 = (let _177_1824 = (FStar_All.pipe_right formals (FStar_List.map (fun _85_2110 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (_177_1824), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_177_1825))
in (

let _85_2118 = (

let env = (

let _85_2113 = env
in {bindings = _85_2113.bindings; depth = _85_2113.depth; tcenv = _85_2113.tcenv; warn = _85_2113.warn; cache = _85_2113.cache; nolabels = _85_2113.nolabels; use_zfuel_name = _85_2113.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_85_2118) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let _85_2128 = (match (formals) with
| [] -> begin
(let _177_1829 = (let _177_1828 = (let _177_1827 = (FStar_SMTEncoding_Term.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _177_1826 -> Some (_177_1826)) _177_1827))
in (push_free_var env lid vname _177_1828))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_177_1829)))
end
| _85_2122 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (let _177_1830 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) _177_1830))
in (

let name_tok_corr = (let _177_1834 = (let _177_1833 = (let _177_1832 = (let _177_1831 = (FStar_SMTEncoding_Term.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::[]), (vars), (_177_1831)))
in (FStar_SMTEncoding_Term.mkForall _177_1832))
in ((_177_1833), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (_177_1834))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (_85_2128) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (_85_2131) with
| (decls2, env) -> begin
(

let _85_2139 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let _85_2135 = (encode_term res_t env')
in (match (_85_2135) with
| (encoded_res_t, decls) -> begin
(let _177_1835 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_177_1835), (decls)))
end)))
in (match (_85_2139) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (let _177_1839 = (let _177_1838 = (let _177_1837 = (let _177_1836 = (FStar_SMTEncoding_Term.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_177_1836)))
in (FStar_SMTEncoding_Term.mkForall _177_1837))
in ((_177_1838), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (_177_1839))
in (

let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _177_1845 = (let _177_1842 = (let _177_1841 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _177_1840 = (varops.next_id ())
in ((vname), (_177_1841), (FStar_SMTEncoding_Term.Term_sort), (_177_1840))))
in (FStar_SMTEncoding_Term.fresh_constructor _177_1842))
in (let _177_1844 = (let _177_1843 = (pretype_axiom vapp vars)
in (_177_1843)::[])
in (_177_1845)::_177_1844))
end else begin
[]
end
in (

let g = (let _177_1850 = (let _177_1849 = (let _177_1848 = (let _177_1847 = (let _177_1846 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_177_1846)
in (FStar_List.append freshness _177_1847))
in (FStar_List.append decls3 _177_1848))
in (FStar_List.append decls2 _177_1849))
in (FStar_List.append decls1 _177_1850))
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

let _85_2150 = (encode_free_var env x t t_norm [])
in (match (_85_2150) with
| (decls, env) -> begin
(

let _85_2155 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_85_2155) with
| (n, x', _85_2154) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, _85_2159) -> begin
((((n), (x))), ([]), (env))
end))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let _85_2169 = (encode_free_var env lid t tt quals)
in (match (_85_2169) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _177_1868 = (let _177_1867 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _177_1867))
in ((_177_1868), (env)))
end else begin
((decls), (env))
end
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _85_2175 lb -> (match (_85_2175) with
| (decls, env) -> begin
(

let _85_2179 = (let _177_1877 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _177_1877 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_85_2179) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env _85_2183 quals -> (match (_85_2183) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let _85_2193 = (FStar_Util.first_N nbinders formals)
in (match (_85_2193) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun _85_2197 _85_2201 -> (match (((_85_2197), (_85_2201))) with
| ((formal, _85_2196), (binder, _85_2200)) -> begin
(let _177_1895 = (let _177_1894 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (_177_1894)))
in FStar_Syntax_Syntax.NT (_177_1895))
end)) formals binders)
in (

let extra_formals = (let _177_1899 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _85_2205 -> (match (_85_2205) with
| (x, i) -> begin
(let _177_1898 = (

let _85_2206 = x
in (let _177_1897 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _85_2206.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _85_2206.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _177_1897}))
in ((_177_1898), (i)))
end))))
in (FStar_All.pipe_right _177_1899 FStar_Syntax_Util.name_binders))
in (

let body = (let _177_1906 = (FStar_Syntax_Subst.compress body)
in (let _177_1905 = (let _177_1900 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _177_1900))
in (let _177_1904 = (let _177_1903 = (let _177_1902 = (FStar_Syntax_Subst.subst subst t)
in _177_1902.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _177_1901 -> Some (_177_1901)) _177_1903))
in (FStar_Syntax_Syntax.extend_app_n _177_1906 _177_1905 _177_1904 body.FStar_Syntax_Syntax.pos))))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (match ((let _177_1917 = (FStar_Syntax_Util.unascribe e)
in _177_1917.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let _85_2225 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_85_2225) with
| (binders, body, opening) -> begin
(match ((let _177_1918 = (FStar_Syntax_Subst.compress t_norm)
in _177_1918.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _85_2232 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_85_2232) with
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

let _85_2239 = (FStar_Util.first_N nformals binders)
in (match (_85_2239) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun _85_2243 _85_2247 -> (match (((_85_2243), (_85_2247))) with
| ((b, _85_2242), (x, _85_2246)) -> begin
(let _177_1922 = (let _177_1921 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (_177_1921)))
in FStar_Syntax_Syntax.NT (_177_1922))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))))
end)))
end else begin
if (nformals > nbinders) then begin
(

let _85_2253 = (eta_expand binders formals body tres)
in (match (_85_2253) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end))
end else begin
((binders), (body), (formals), (tres))
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _85_2256) -> begin
(aux norm x.FStar_Syntax_Syntax.sort)
end
| _85_2260 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _85_2263 -> begin
(let _177_1925 = (let _177_1924 = (FStar_Syntax_Print.term_to_string e)
in (let _177_1923 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _177_1924 _177_1923)))
in (FStar_All.failwith _177_1925))
end)
end))
end
| _85_2265 -> begin
(match ((let _177_1926 = (FStar_Syntax_Subst.compress t_norm)
in _177_1926.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let _85_2272 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_85_2272) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let _85_2276 = (eta_expand [] formals e tres)
in (match (_85_2276) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end)))
end))
end
| _85_2278 -> begin
(([]), (e), ([]), (t_norm))
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

let _85_2306 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _85_2293 lb -> (match (_85_2293) with
| (toks, typs, decls, env) -> begin
(

let _85_2295 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let _85_2301 = (let _177_1931 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _177_1931 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_85_2301) with
| (tok, decl, env) -> begin
(let _177_1934 = (let _177_1933 = (let _177_1932 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((_177_1932), (tok)))
in (_177_1933)::toks)
in ((_177_1934), ((t_norm)::typs), ((decl)::decls), (env)))
end))))
end)) (([]), ([]), ([]), (env))))
in (match (_85_2306) with
| (toks, typs, decls, env) -> begin
(

let toks = (FStar_List.rev toks)
in (

let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_15 -> (match (_85_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _85_2313 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _177_1937 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _177_1937)))))) then begin
((decls), (env))
end else begin
if (not (is_rec)) then begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = _85_2323; FStar_Syntax_Syntax.lbunivs = _85_2321; FStar_Syntax_Syntax.lbtyp = _85_2319; FStar_Syntax_Syntax.lbeff = _85_2317; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let _85_2343 = (destruct_bound_function flid t_norm e)
in (match (_85_2343) with
| (binders, body, _85_2340, _85_2342) -> begin
(

let _85_2350 = (encode_binders None binders env)
in (match (_85_2350) with
| (vars, guards, env', binder_decls, _85_2349) -> begin
(

let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
end
| _85_2353 -> begin
(let _177_1939 = (let _177_1938 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((f), (_177_1938)))
in (FStar_SMTEncoding_Term.mkApp _177_1939))
end)
in (

let _85_2359 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _177_1941 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _177_1940 = (encode_formula body env')
in ((_177_1941), (_177_1940))))
end else begin
(let _177_1942 = (encode_term body env')
in ((app), (_177_1942)))
end
in (match (_85_2359) with
| (app, (body, decls2)) -> begin
(

let eqn = (let _177_1948 = (let _177_1947 = (let _177_1944 = (let _177_1943 = (FStar_SMTEncoding_Term.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (_177_1943)))
in (FStar_SMTEncoding_Term.mkForall _177_1944))
in (let _177_1946 = (let _177_1945 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_177_1945))
in ((_177_1947), (_177_1946), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (_177_1948))
in (let _177_1953 = (let _177_1952 = (let _177_1951 = (let _177_1950 = (let _177_1949 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) _177_1949))
in (FStar_List.append decls2 _177_1950))
in (FStar_List.append binder_decls _177_1951))
in (FStar_List.append decls _177_1952))
in ((_177_1953), (env))))
end)))
end))
end))))
end
| _85_2362 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(

let fuel = (let _177_1954 = (varops.fresh "fuel")
in ((_177_1954), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (

let env0 = env
in (

let _85_2380 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _85_2368 _85_2373 -> (match (((_85_2368), (_85_2373))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (varops.new_fvar flid)
in (

let gtok = (varops.new_fvar flid)
in (

let env = (let _177_1959 = (let _177_1958 = (FStar_SMTEncoding_Term.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _177_1957 -> Some (_177_1957)) _177_1958))
in (push_free_var env flid gtok _177_1959))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (_85_2380) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 _85_2389 t_norm _85_2400 -> (match (((_85_2389), (_85_2400))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _85_2399; FStar_Syntax_Syntax.lbunivs = _85_2397; FStar_Syntax_Syntax.lbtyp = _85_2395; FStar_Syntax_Syntax.lbeff = _85_2393; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let _85_2405 = (destruct_bound_function flid t_norm e)
in (match (_85_2405) with
| (binders, body, formals, tres) -> begin
(

let _85_2412 = (encode_binders None binders env)
in (match (_85_2412) with
| (vars, guards, env', binder_decls, _85_2411) -> begin
(

let decl_g = (let _177_1970 = (let _177_1969 = (let _177_1968 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_177_1968)
in ((g), (_177_1969), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (_177_1970))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let app = (FStar_SMTEncoding_Term.mkApp ((f), (vars_tm)))
in (

let gsapp = (let _177_1973 = (let _177_1972 = (let _177_1971 = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_177_1971)::vars_tm)
in ((g), (_177_1972)))
in (FStar_SMTEncoding_Term.mkApp _177_1973))
in (

let gmax = (let _177_1976 = (let _177_1975 = (let _177_1974 = (FStar_SMTEncoding_Term.mkApp (("MaxFuel"), ([])))
in (_177_1974)::vars_tm)
in ((g), (_177_1975)))
in (FStar_SMTEncoding_Term.mkApp _177_1976))
in (

let _85_2422 = (encode_term body env')
in (match (_85_2422) with
| (body_tm, decls2) -> begin
(

let eqn_g = (let _177_1982 = (let _177_1981 = (let _177_1978 = (let _177_1977 = (FStar_SMTEncoding_Term.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_177_1977)))
in (FStar_SMTEncoding_Term.mkForall _177_1978))
in (let _177_1980 = (let _177_1979 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_177_1979))
in ((_177_1981), (_177_1980), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (_177_1982))
in (

let eqn_f = (let _177_1986 = (let _177_1985 = (let _177_1984 = (let _177_1983 = (FStar_SMTEncoding_Term.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_177_1983)))
in (FStar_SMTEncoding_Term.mkForall _177_1984))
in ((_177_1985), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_177_1986))
in (

let eqn_g' = (let _177_1995 = (let _177_1994 = (let _177_1993 = (let _177_1992 = (let _177_1991 = (let _177_1990 = (let _177_1989 = (let _177_1988 = (let _177_1987 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_177_1987)::vars_tm)
in ((g), (_177_1988)))
in (FStar_SMTEncoding_Term.mkApp _177_1989))
in ((gsapp), (_177_1990)))
in (FStar_SMTEncoding_Term.mkEq _177_1991))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_177_1992)))
in (FStar_SMTEncoding_Term.mkForall _177_1993))
in ((_177_1994), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (_177_1995))
in (

let _85_2445 = (

let _85_2432 = (encode_binders None formals env0)
in (match (_85_2432) with
| (vars, v_guards, env, binder_decls, _85_2431) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Term.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (let _177_1996 = (FStar_SMTEncoding_Term.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _177_1996 ((fuel)::vars)))
in (let _177_2000 = (let _177_1999 = (let _177_1998 = (let _177_1997 = (FStar_SMTEncoding_Term.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_177_1997)))
in (FStar_SMTEncoding_Term.mkForall _177_1998))
in ((_177_1999), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_tokem_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (_177_2000)))
in (

let _85_2442 = (

let _85_2439 = (encode_term_pred None tres env gapp)
in (match (_85_2439) with
| (g_typing, d3) -> begin
(let _177_2008 = (let _177_2007 = (let _177_2006 = (let _177_2005 = (let _177_2004 = (let _177_2003 = (let _177_2002 = (let _177_2001 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in ((_177_2001), (g_typing)))
in (FStar_SMTEncoding_Term.mkImp _177_2002))
in ((((gapp)::[])::[]), ((fuel)::vars), (_177_2003)))
in (FStar_SMTEncoding_Term.mkForall _177_2004))
in ((_177_2005), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_177_2006))
in (_177_2007)::[])
in ((d3), (_177_2008)))
end))
in (match (_85_2442) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (_85_2445) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end))
end))
end))
in (

let _85_2461 = (let _177_2011 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _85_2449 _85_2453 -> (match (((_85_2449), (_85_2453))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let _85_2457 = (encode_one_binding env0 gtok ty bs)
in (match (_85_2457) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _177_2011))
in (match (_85_2461) with
| (decls, eqns, env0) -> begin
(

let _85_2470 = (let _177_2013 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _177_2013 (FStar_List.partition (fun _85_16 -> (match (_85_16) with
| FStar_SMTEncoding_Term.DeclFun (_85_2464) -> begin
true
end
| _85_2467 -> begin
false
end)))))
in (match (_85_2470) with
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

let msg = (let _177_2016 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _177_2016 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let _85_2474 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _177_2025 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _177_2025))
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

let _85_2482 = (encode_sigelt' env se)
in (match (_85_2482) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _177_2028 = (let _177_2027 = (let _177_2026 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_177_2026))
in (_177_2027)::[])
in ((_177_2028), (e)))
end
| _85_2485 -> begin
(let _177_2035 = (let _177_2034 = (let _177_2030 = (let _177_2029 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_177_2029))
in (_177_2030)::g)
in (let _177_2033 = (let _177_2032 = (let _177_2031 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_177_2031))
in (_177_2032)::[])
in (FStar_List.append _177_2034 _177_2033)))
in ((_177_2035), (e)))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_85_2491) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _85_2507) -> begin
if (let _177_2040 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _177_2040 Prims.op_Negation)) then begin
(([]), (env))
end else begin
(

let encode_monad_op = (fun tm name env -> (

let repr_name = (fun ed -> (FStar_Ident.lid_of_ids (FStar_List.append (FStar_Ident.ids_of_lid ed.FStar_Syntax_Syntax.mname) (((FStar_Ident.id_of_text (Prims.strcat name "_repr")))::[]))))
in (

let _85_2520 = (let _177_2049 = (repr_name ed)
in (new_term_constant_and_tok_from_lid env _177_2049))
in (match (_85_2520) with
| (br_name, _85_2518, env) -> begin
(

let _85_2523 = (encode_term (Prims.snd tm) env)
in (match (_85_2523) with
| (tm, decls) -> begin
(

let xs = if (name = "bind") then begin
((("@x0"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x1"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x2"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x3"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x4"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x5"), (FStar_SMTEncoding_Term.Term_sort)))::[]
end else begin
((("@x0"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x1"), (FStar_SMTEncoding_Term.Term_sort)))::((("@x2"), (FStar_SMTEncoding_Term.Term_sort)))::[]
end
in (

let m_decl = (let _177_2051 = (let _177_2050 = (FStar_All.pipe_right xs (FStar_List.map Prims.snd))
in ((br_name), (_177_2050), (FStar_SMTEncoding_Term.Term_sort), (Some (name))))
in FStar_SMTEncoding_Term.DeclFun (_177_2051))
in (

let eqn = (

let app = (let _177_2054 = (let _177_2053 = (let _177_2052 = (FStar_All.pipe_right xs (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((FStar_SMTEncoding_Term.Var (br_name)), (_177_2052)))
in FStar_SMTEncoding_Term.App (_177_2053))
in (FStar_SMTEncoding_Term.mk _177_2054))
in (let _177_2060 = (let _177_2059 = (let _177_2058 = (let _177_2057 = (let _177_2056 = (let _177_2055 = (mk_Apply tm xs)
in ((app), (_177_2055)))
in (FStar_SMTEncoding_Term.mkEq _177_2056))
in ((((app)::[])::[]), (xs), (_177_2057)))
in (FStar_SMTEncoding_Term.mkForall _177_2058))
in ((_177_2059), (Some ((Prims.strcat name " equality"))), (Some ((Prims.strcat br_name "_equality")))))
in FStar_SMTEncoding_Term.Assume (_177_2060)))
in ((env), ((m_decl)::(eqn)::[])))))
end))
end))))
in (

let encode_action = (fun env a -> (

let _85_2534 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (_85_2534) with
| (aname, atok, env) -> begin
(

let _85_2538 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (_85_2538) with
| (formals, _85_2537) -> begin
(

let _85_2541 = (encode_term a.FStar_Syntax_Syntax.action_defn env)
in (match (_85_2541) with
| (tm, decls) -> begin
(

let a_decls = (let _177_2068 = (let _177_2067 = (let _177_2066 = (FStar_All.pipe_right formals (FStar_List.map (fun _85_2542 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (_177_2066), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (_177_2067))
in (_177_2068)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let _85_2556 = (let _177_2070 = (FStar_All.pipe_right formals (FStar_List.map (fun _85_2548 -> (match (_85_2548) with
| (bv, _85_2547) -> begin
(

let _85_2553 = (gen_term_var env bv)
in (match (_85_2553) with
| (xxsym, xx, _85_2552) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right _177_2070 FStar_List.split))
in (match (_85_2556) with
| (xs_sorts, xs) -> begin
(

let app = (let _177_2074 = (let _177_2073 = (let _177_2072 = (let _177_2071 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Var (aname)), (xs)))))
in (_177_2071)::[])
in ((FStar_SMTEncoding_Term.Var ("Reify")), (_177_2072)))
in FStar_SMTEncoding_Term.App (_177_2073))
in (FStar_All.pipe_right _177_2074 FStar_SMTEncoding_Term.mk))
in (

let a_eq = (let _177_2080 = (let _177_2079 = (let _177_2078 = (let _177_2077 = (let _177_2076 = (let _177_2075 = (mk_Apply tm xs_sorts)
in ((app), (_177_2075)))
in (FStar_SMTEncoding_Term.mkEq _177_2076))
in ((((app)::[])::[]), (xs_sorts), (_177_2077)))
in (FStar_SMTEncoding_Term.mkForall _177_2078))
in ((_177_2079), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (_177_2080))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Term.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (let _177_2084 = (let _177_2083 = (let _177_2082 = (let _177_2081 = (FStar_SMTEncoding_Term.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (_177_2081)))
in (FStar_SMTEncoding_Term.mkForall _177_2082))
in ((_177_2083), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (_177_2084))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let _85_2564 = (encode_monad_op ed.FStar_Syntax_Syntax.bind_repr "bind" env)
in (match (_85_2564) with
| (env, decls0) -> begin
(

let _85_2567 = (encode_monad_op ed.FStar_Syntax_Syntax.return_repr "return" env)
in (match (_85_2567) with
| (env, decls1) -> begin
(

let _85_2570 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (_85_2570) with
| (env, decls2) -> begin
(((FStar_List.append decls0 (FStar_List.append decls1 (FStar_List.flatten decls2)))), (env))
end))
end))
end))))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _85_2573, _85_2575, _85_2577, _85_2579) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let _85_2585 = (new_term_constant_and_tok_from_lid env lid)
in (match (_85_2585) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _85_2588, t, quals, _85_2592) -> begin
(

let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_17 -> (match (_85_17) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _85_2605 -> begin
false
end))))))
in if will_encode_definition then begin
(([]), (env))
end else begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let _85_2610 = (encode_top_level_val env fv t quals)
in (match (_85_2610) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Term.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (let _177_2087 = (let _177_2086 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _177_2086))
in ((_177_2087), (env)))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _85_2616, _85_2618) -> begin
(

let _85_2623 = (encode_formula f env)
in (match (_85_2623) with
| (f, decls) -> begin
(

let g = (let _177_2094 = (let _177_2093 = (let _177_2092 = (let _177_2089 = (let _177_2088 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _177_2088))
in Some (_177_2089))
in (let _177_2091 = (let _177_2090 = (varops.fresh (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (_177_2090))
in ((f), (_177_2092), (_177_2091))))
in FStar_SMTEncoding_Term.Assume (_177_2093))
in (_177_2094)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _85_2628, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let _85_2641 = (FStar_Util.fold_map (fun env lb -> (

let lid = (let _177_2098 = (let _177_2097 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _177_2097.FStar_Syntax_Syntax.fv_name)
in _177_2098.FStar_Syntax_Syntax.v)
in if (let _177_2099 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _177_2099)) then begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let _85_2638 = (encode_sigelt' env val_decl)
in (match (_85_2638) with
| (decls, env) -> begin
((env), (decls))
end)))
end else begin
((env), ([]))
end)) env (Prims.snd lbs))
in (match (_85_2641) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((_85_2643, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _85_2651; FStar_Syntax_Syntax.lbtyp = _85_2649; FStar_Syntax_Syntax.lbeff = _85_2647; FStar_Syntax_Syntax.lbdef = _85_2645})::[]), _85_2658, _85_2660, _85_2662) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let _85_2668 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_85_2668) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (

let valid_b2t_x = (let _177_2102 = (let _177_2101 = (let _177_2100 = (FStar_SMTEncoding_Term.mkApp (("Prims.b2t"), ((x)::[])))
in (_177_2100)::[])
in (("Valid"), (_177_2101)))
in (FStar_SMTEncoding_Term.mkApp _177_2102))
in (

let decls = (let _177_2110 = (let _177_2109 = (let _177_2108 = (let _177_2107 = (let _177_2106 = (let _177_2105 = (let _177_2104 = (let _177_2103 = (FStar_SMTEncoding_Term.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_177_2103)))
in (FStar_SMTEncoding_Term.mkEq _177_2104))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_177_2105)))
in (FStar_SMTEncoding_Term.mkForall _177_2106))
in ((_177_2107), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (_177_2108))
in (_177_2109)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::_177_2110)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_85_2674, _85_2676, _85_2678, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_18 -> (match (_85_18) with
| FStar_Syntax_Syntax.Discriminator (_85_2684) -> begin
true
end
| _85_2687 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (_85_2689, _85_2691, lids, quals) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> ((let _177_2113 = (FStar_List.hd l.FStar_Ident.ns)
in _177_2113.FStar_Ident.idText) = "Prims")))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_19 -> (match (_85_19) with
| FStar_Syntax_Syntax.Inline -> begin
true
end
| _85_2700 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _85_2706, _85_2708, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_20 -> (match (_85_20) with
| FStar_Syntax_Syntax.Projector (_85_2714) -> begin
true
end
| _85_2717 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_85_2721) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _85_2730, _85_2732, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(match ((let _177_2116 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in _177_2116.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _85_2739) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None)))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let _85_2747 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (_85_2747) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let _85_2748 = env.tcenv
in {FStar_TypeChecker_Env.solver = _85_2748.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _85_2748.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _85_2748.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _85_2748.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _85_2748.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _85_2748.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _85_2748.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _85_2748.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _85_2748.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _85_2748.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _85_2748.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _85_2748.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _85_2748.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _85_2748.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _85_2748.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _85_2748.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _85_2748.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _85_2748.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _85_2748.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _85_2748.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _85_2748.FStar_TypeChecker_Env.use_bv_sorts}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (let _177_2117 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals _177_2117)))
end))
in (

let lb = (

let _85_2752 = lb
in {FStar_Syntax_Syntax.lbname = _85_2752.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _85_2752.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = _85_2752.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (encode_top_level_let env ((false), ((lb)::[])) quals))))))
end
| _85_2756 -> begin
(([]), (env))
end)
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _85_2761, _85_2763, quals) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _85_2769, _85_2771, _85_2773) -> begin
(

let _85_2778 = (encode_signature env ses)
in (match (_85_2778) with
| (g, env) -> begin
(

let _85_2792 = (FStar_All.pipe_right g (FStar_List.partition (fun _85_21 -> (match (_85_21) with
| FStar_SMTEncoding_Term.Assume (_85_2781, Some ("inversion axiom"), _85_2785) -> begin
false
end
| _85_2789 -> begin
true
end))))
in (match (_85_2792) with
| (g', inversions) -> begin
(

let _85_2801 = (FStar_All.pipe_right g' (FStar_List.partition (fun _85_22 -> (match (_85_22) with
| FStar_SMTEncoding_Term.DeclFun (_85_2795) -> begin
true
end
| _85_2798 -> begin
false
end))))
in (match (_85_2801) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _85_2804, tps, k, _85_2808, datas, quals, _85_2812) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _85_23 -> (match (_85_23) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _85_2819 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(

let _85_2831 = c
in (match (_85_2831) with
| (name, args, _85_2826, _85_2828, _85_2830) -> begin
(let _177_2125 = (let _177_2124 = (let _177_2123 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_177_2123), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_177_2124))
in (_177_2125)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (

let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _177_2131 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _177_2131 FStar_Option.isNone))))) then begin
[]
end else begin
(

let _85_2838 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_85_2838) with
| (xxsym, xx) -> begin
(

let _85_2874 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _85_2841 l -> (match (_85_2841) with
| (out, decls) -> begin
(

let _85_2846 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_85_2846) with
| (_85_2844, data_t) -> begin
(

let _85_2849 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_85_2849) with
| (args, res) -> begin
(

let indices = (match ((let _177_2134 = (FStar_Syntax_Subst.compress res)
in _177_2134.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_85_2851, indices) -> begin
indices
end
| _85_2856 -> begin
[]
end)
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _85_2862 -> (match (_85_2862) with
| (x, _85_2861) -> begin
(let _177_2139 = (let _177_2138 = (let _177_2137 = (mk_term_projector_name l x)
in ((_177_2137), ((xx)::[])))
in (FStar_SMTEncoding_Term.mkApp _177_2138))
in (push_term_var env x _177_2139))
end)) env))
in (

let _85_2866 = (encode_args indices env)
in (match (_85_2866) with
| (indices, decls') -> begin
(

let _85_2867 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (

let eqs = (let _177_2144 = (FStar_List.map2 (fun v a -> (let _177_2143 = (let _177_2142 = (FStar_SMTEncoding_Term.mkFreeV v)
in ((_177_2142), (a)))
in (FStar_SMTEncoding_Term.mkEq _177_2143))) vars indices)
in (FStar_All.pipe_right _177_2144 FStar_SMTEncoding_Term.mk_and_l))
in (let _177_2149 = (let _177_2148 = (let _177_2147 = (let _177_2146 = (let _177_2145 = (mk_data_tester env l xx)
in ((_177_2145), (eqs)))
in (FStar_SMTEncoding_Term.mkAnd _177_2146))
in ((out), (_177_2147)))
in (FStar_SMTEncoding_Term.mkOr _177_2148))
in ((_177_2149), ((FStar_List.append decls decls'))))))
end))))
end))
end))
end)) ((FStar_SMTEncoding_Term.mkFalse), ([]))))
in (match (_85_2874) with
| (data_ax, decls) -> begin
(

let _85_2877 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_2877) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = if ((FStar_List.length datas) > 1) then begin
(let _177_2150 = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _177_2150 xx tapp))
end else begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end
in (let _177_2157 = (let _177_2156 = (let _177_2153 = (let _177_2152 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _177_2151 = (FStar_SMTEncoding_Term.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (_177_2152), (_177_2151))))
in (FStar_SMTEncoding_Term.mkForall _177_2153))
in (let _177_2155 = (let _177_2154 = (varops.fresh (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (_177_2154))
in ((_177_2156), (Some ("inversion axiom")), (_177_2155))))
in FStar_SMTEncoding_Term.Assume (_177_2157)))
in (

let pattern_guarded_inversion = if ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > 1)) then begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Term.mkApp (("Prims.inversion"), ((tapp)::[])))
in (let _177_2165 = (let _177_2164 = (let _177_2163 = (let _177_2160 = (let _177_2159 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _177_2158 = (FStar_SMTEncoding_Term.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (_177_2159), (_177_2158))))
in (FStar_SMTEncoding_Term.mkForall _177_2160))
in (let _177_2162 = (let _177_2161 = (varops.fresh (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (_177_2161))
in ((_177_2163), (Some ("inversion axiom")), (_177_2162))))
in FStar_SMTEncoding_Term.Assume (_177_2164))
in (_177_2165)::[])))
end else begin
[]
end
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)
in (

let _85_2891 = (match ((let _177_2166 = (FStar_Syntax_Subst.compress k)
in _177_2166.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| _85_2888 -> begin
((tps), (k))
end)
in (match (_85_2891) with
| (formals, res) -> begin
(

let _85_2894 = (FStar_Syntax_Subst.open_term formals res)
in (match (_85_2894) with
| (formals, res) -> begin
(

let _85_2901 = (encode_binders None formals env)
in (match (_85_2901) with
| (vars, guards, env', binder_decls, _85_2900) -> begin
(

let _85_2905 = (new_term_constant_and_tok_from_lid env t)
in (match (_85_2905) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Term.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let tapp = (let _177_2168 = (let _177_2167 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((tname), (_177_2167)))
in (FStar_SMTEncoding_Term.mkApp _177_2168))
in (

let _85_2926 = (

let tname_decl = (let _177_2172 = (let _177_2171 = (FStar_All.pipe_right vars (FStar_List.map (fun _85_2911 -> (match (_85_2911) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _177_2170 = (varops.next_id ())
in ((tname), (_177_2171), (FStar_SMTEncoding_Term.Term_sort), (_177_2170), (false))))
in (constructor_or_logic_type_decl _177_2172))
in (

let _85_2923 = (match (vars) with
| [] -> begin
(let _177_2176 = (let _177_2175 = (let _177_2174 = (FStar_SMTEncoding_Term.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _177_2173 -> Some (_177_2173)) _177_2174))
in (push_free_var env t tname _177_2175))
in (([]), (_177_2176)))
end
| _85_2915 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (let _177_2177 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) _177_2177))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (let _177_2181 = (let _177_2180 = (let _177_2179 = (let _177_2178 = (FStar_SMTEncoding_Term.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_177_2178)))
in (FStar_SMTEncoding_Term.mkForall' _177_2179))
in ((_177_2180), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_177_2181))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (_85_2923) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (_85_2926) with
| (decls, env) -> begin
(

let kindingAx = (

let _85_2929 = (encode_term_pred None res env' tapp)
in (match (_85_2929) with
| (k, decls) -> begin
(

let karr = if ((FStar_List.length formals) > 0) then begin
(let _177_2185 = (let _177_2184 = (let _177_2183 = (let _177_2182 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _177_2182))
in ((_177_2183), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_177_2184))
in (_177_2185)::[])
end else begin
[]
end
in (let _177_2192 = (let _177_2191 = (let _177_2190 = (let _177_2189 = (let _177_2188 = (let _177_2187 = (let _177_2186 = (FStar_SMTEncoding_Term.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_177_2186)))
in (FStar_SMTEncoding_Term.mkForall _177_2187))
in ((_177_2188), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_177_2189))
in (_177_2190)::[])
in (FStar_List.append karr _177_2191))
in (FStar_List.append decls _177_2192)))
end))
in (

let aux = (let _177_2196 = (let _177_2195 = (inversion_axioms tapp vars)
in (let _177_2194 = (let _177_2193 = (pretype_axiom tapp vars)
in (_177_2193)::[])
in (FStar_List.append _177_2195 _177_2194)))
in (FStar_List.append kindingAx _177_2196))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _85_2936, _85_2938, _85_2940, _85_2942, _85_2944, _85_2946, _85_2948) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _85_2953, t, _85_2956, n_tps, quals, _85_2960, drange) -> begin
(

let _85_2967 = (new_term_constant_and_tok_from_lid env d)
in (match (_85_2967) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Term.mkApp ((ddtok), ([])))
in (

let _85_2971 = (FStar_Syntax_Util.arrow_formals t)
in (match (_85_2971) with
| (formals, t_res) -> begin
(

let _85_2974 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_85_2974) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let _85_2981 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_85_2981) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _177_2198 = (mk_term_projector_name d x)
in ((_177_2198), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (let _177_2200 = (let _177_2199 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (_177_2199), (true)))
in (FStar_All.pipe_right _177_2200 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (

let _85_2991 = (encode_term_pred None t env ddtok_tm)
in (match (_85_2991) with
| (tok_typing, decls3) -> begin
(

let _85_2998 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_85_2998) with
| (vars', guards', env'', decls_formals, _85_2997) -> begin
(

let _85_3003 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_85_3003) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _85_3007 -> begin
(let _177_2202 = (let _177_2201 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) _177_2201))
in (_177_2202)::[])
end)
in (

let encode_elim = (fun _85_3010 -> (match (()) with
| () -> begin
(

let _85_3013 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_85_3013) with
| (head, args) -> begin
(match ((let _177_2205 = (FStar_Syntax_Subst.compress head)
in _177_2205.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let _85_3031 = (encode_args args env')
in (match (_85_3031) with
| (encoded_args, arg_decls) -> begin
(

let _85_3046 = (FStar_List.fold_left (fun _85_3035 arg -> (match (_85_3035) with
| (env, arg_vars, eqns) -> begin
(

let _85_3041 = (let _177_2208 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _177_2208))
in (match (_85_3041) with
| (_85_3038, xv, env) -> begin
(let _177_2210 = (let _177_2209 = (FStar_SMTEncoding_Term.mkEq ((arg), (xv)))
in (_177_2209)::eqns)
in ((env), ((xv)::arg_vars), (_177_2210)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (_85_3046) with
| (_85_3043, arg_vars, eqns) -> begin
(

let arg_vars = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_Term.mkApp ((encoded_head), (arg_vars)))
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (

let typing_inversion = (let _177_2217 = (let _177_2216 = (let _177_2215 = (let _177_2214 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _177_2213 = (let _177_2212 = (let _177_2211 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_177_2211)))
in (FStar_SMTEncoding_Term.mkImp _177_2212))
in ((((ty_pred)::[])::[]), (_177_2214), (_177_2213))))
in (FStar_SMTEncoding_Term.mkForall _177_2215))
in ((_177_2216), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_177_2217))
in (

let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(

let x = (let _177_2218 = (varops.fresh "x")
in ((_177_2218), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _177_2230 = (let _177_2229 = (let _177_2226 = (let _177_2225 = (let _177_2220 = (let _177_2219 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_177_2219)::[])
in (_177_2220)::[])
in (let _177_2224 = (let _177_2223 = (let _177_2222 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _177_2221 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in ((_177_2222), (_177_2221))))
in (FStar_SMTEncoding_Term.mkImp _177_2223))
in ((_177_2225), ((x)::[]), (_177_2224))))
in (FStar_SMTEncoding_Term.mkForall _177_2226))
in (let _177_2228 = (let _177_2227 = (varops.fresh "lextop")
in Some (_177_2227))
in ((_177_2229), (Some ("lextop is top")), (_177_2228))))
in FStar_SMTEncoding_Term.Assume (_177_2230))))
end else begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _177_2233 = (let _177_2232 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _177_2232 dapp))
in (_177_2233)::[])
end
| _85_3060 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _177_2240 = (let _177_2239 = (let _177_2238 = (let _177_2237 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _177_2236 = (let _177_2235 = (let _177_2234 = (FStar_SMTEncoding_Term.mk_and_l prec)
in ((ty_pred), (_177_2234)))
in (FStar_SMTEncoding_Term.mkImp _177_2235))
in ((((ty_pred)::[])::[]), (_177_2237), (_177_2236))))
in (FStar_SMTEncoding_Term.mkForall _177_2238))
in ((_177_2239), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_177_2240)))
end
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| _85_3064 -> begin
(

let _85_3065 = (let _177_2243 = (let _177_2242 = (FStar_Syntax_Print.lid_to_string d)
in (let _177_2241 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _177_2242 _177_2241)))
in (FStar_TypeChecker_Errors.warn drange _177_2243))
in (([]), ([])))
end)
end))
end))
in (

let _85_3069 = (encode_elim ())
in (match (_85_3069) with
| (decls2, elim) -> begin
(

let g = (let _177_2270 = (let _177_2269 = (let _177_2268 = (let _177_2267 = (let _177_2248 = (let _177_2247 = (let _177_2246 = (let _177_2245 = (let _177_2244 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _177_2244))
in Some (_177_2245))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (_177_2246)))
in FStar_SMTEncoding_Term.DeclFun (_177_2247))
in (_177_2248)::[])
in (let _177_2266 = (let _177_2265 = (let _177_2264 = (let _177_2263 = (let _177_2262 = (let _177_2261 = (let _177_2260 = (let _177_2252 = (let _177_2251 = (let _177_2250 = (let _177_2249 = (FStar_SMTEncoding_Term.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_177_2249)))
in (FStar_SMTEncoding_Term.mkForall _177_2250))
in ((_177_2251), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_177_2252))
in (let _177_2259 = (let _177_2258 = (let _177_2257 = (let _177_2256 = (let _177_2255 = (let _177_2254 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (let _177_2253 = (FStar_SMTEncoding_Term.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_177_2254), (_177_2253))))
in (FStar_SMTEncoding_Term.mkForall _177_2255))
in ((_177_2256), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_177_2257))
in (_177_2258)::[])
in (_177_2260)::_177_2259))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::_177_2261)
in (FStar_List.append _177_2262 elim))
in (FStar_List.append decls_pred _177_2263))
in (FStar_List.append decls_formals _177_2264))
in (FStar_List.append proxy_fresh _177_2265))
in (FStar_List.append _177_2267 _177_2266)))
in (FStar_List.append decls3 _177_2268))
in (FStar_List.append decls2 _177_2269))
in (FStar_List.append binder_decls _177_2270))
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
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _85_3075 se -> (match (_85_3075) with
| (g, env) -> begin
(

let _85_3079 = (encode_sigelt env se)
in (match (_85_3079) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (

let encode_binding = (fun b _85_3086 -> (match (_85_3086) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_85_3088) -> begin
(([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let _85_3095 = (new_term_constant env x)
in (match (_85_3095) with
| (xxsym, xx, env') -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let _85_3097 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _177_2285 = (FStar_Syntax_Print.bv_to_string x)
in (let _177_2284 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _177_2283 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _177_2285 _177_2284 _177_2283))))
end else begin
()
end
in (

let _85_3101 = (encode_term_pred None t1 env xx)
in (match (_85_3101) with
| (t, decls') -> begin
(

let caption = if (FStar_Options.log_queries ()) then begin
(let _177_2289 = (let _177_2288 = (FStar_Syntax_Print.bv_to_string x)
in (let _177_2287 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _177_2286 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _177_2288 _177_2287 _177_2286))))
in Some (_177_2289))
end else begin
None
end
in (

let ax = (

let a_name = Some ((Prims.strcat "binder_" xxsym))
in FStar_SMTEncoding_Term.Assume (((t), (a_name), (a_name))))
in (

let g = (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun (((xxsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((ax)::[])))
in (((FStar_List.append decls g)), (env')))))
end))))
end))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_85_3108, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let _85_3117 = (encode_free_var env fv t t_norm [])
in (match (_85_3117) with
| (g, env') -> begin
(((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let _85_3131 = (encode_sigelt env se)
in (match (_85_3131) with
| (g, env') -> begin
(((FStar_List.append decls g)), (env'))
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings (([]), (env)))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _85_3138 -> (match (_85_3138) with
| (l, _85_3135, _85_3137) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _85_3145 -> (match (_85_3145) with
| (l, _85_3142, _85_3144) -> begin
(let _177_2297 = (FStar_All.pipe_left (fun _177_2293 -> FStar_SMTEncoding_Term.Echo (_177_2293)) (Prims.fst l))
in (let _177_2296 = (let _177_2295 = (let _177_2294 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_177_2294))
in (_177_2295)::[])
in (_177_2297)::_177_2296))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _177_2302 = (let _177_2301 = (let _177_2300 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _177_2300; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_177_2301)::[])
in (FStar_ST.op_Colon_Equals last_env _177_2302)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_85_3151 -> begin
(

let _85_3154 = e
in {bindings = _85_3154.bindings; depth = _85_3154.depth; tcenv = tcenv; warn = _85_3154.warn; cache = _85_3154.cache; nolabels = _85_3154.nolabels; use_zfuel_name = _85_3154.use_zfuel_name; encode_non_total_function_typ = _85_3154.encode_non_total_function_typ})
end))


let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_85_3160)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))


let push_env : Prims.unit  ->  Prims.unit = (fun _85_3162 -> (match (()) with
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

let _85_3168 = hd
in {bindings = _85_3168.bindings; depth = _85_3168.depth; tcenv = _85_3168.tcenv; warn = _85_3168.warn; cache = refs; nolabels = _85_3168.nolabels; use_zfuel_name = _85_3168.use_zfuel_name; encode_non_total_function_typ = _85_3168.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))


let pop_env : Prims.unit  ->  Prims.unit = (fun _85_3171 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_85_3175)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))


let mark_env : Prims.unit  ->  Prims.unit = (fun _85_3177 -> (match (()) with
| () -> begin
(push_env ())
end))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _85_3178 -> (match (()) with
| () -> begin
(pop_env ())
end))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _85_3179 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_85_3182)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _85_3187 -> begin
(FStar_All.failwith "Impossible")
end)
end))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let _85_3189 = (init_env tcenv)
in (

let _85_3191 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_3194 = (push_env ())
in (

let _85_3196 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_3199 = (let _177_2323 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _177_2323))
in (

let _85_3201 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_3204 = (mark_env ())
in (

let _85_3206 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_3209 = (reset_mark_env ())
in (

let _85_3211 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))


let commit_mark = (fun msg -> (

let _85_3214 = (commit_mark_env ())
in (

let _85_3216 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _177_2339 = (let _177_2338 = (let _177_2337 = (let _177_2336 = (let _177_2335 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _177_2335 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _177_2336 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _177_2337))
in FStar_SMTEncoding_Term.Caption (_177_2338))
in (_177_2339)::decls)
end else begin
decls
end)
in (

let env = (get_env tcenv)
in (

let _85_3225 = (encode_sigelt env se)
in (match (_85_3225) with
| (decls, env) -> begin
(

let _85_3226 = (set_env env)
in (let _177_2340 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _177_2340)))
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (

let _85_3231 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _177_2345 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _177_2345))
end else begin
()
end
in (

let env = (get_env tcenv)
in (

let _85_3238 = (encode_signature (

let _85_3234 = env
in {bindings = _85_3234.bindings; depth = _85_3234.depth; tcenv = _85_3234.tcenv; warn = false; cache = _85_3234.cache; nolabels = _85_3234.nolabels; use_zfuel_name = _85_3234.use_zfuel_name; encode_non_total_function_typ = _85_3234.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_85_3238) with
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

let _85_3244 = (set_env (

let _85_3242 = env
in {bindings = _85_3242.bindings; depth = _85_3242.depth; tcenv = _85_3242.tcenv; warn = true; cache = _85_3242.cache; nolabels = _85_3242.nolabels; use_zfuel_name = _85_3242.use_zfuel_name; encode_non_total_function_typ = _85_3242.encode_non_total_function_typ}))
in (

let _85_3246 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> (

let _85_3252 = (let _177_2363 = (let _177_2362 = (FStar_TypeChecker_Env.current_module tcenv)
in _177_2362.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name _177_2363))
in (

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let _85_3277 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let _85_3266 = (aux rest)
in (match (_85_3266) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _177_2369 = (let _177_2368 = (FStar_Syntax_Syntax.mk_binder (

let _85_3268 = x
in {FStar_Syntax_Syntax.ppname = _85_3268.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _85_3268.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_177_2368)::out)
in ((_177_2369), (rest))))
end))
end
| _85_3271 -> begin
(([]), (bindings))
end))
in (

let _85_3274 = (aux bindings)
in (match (_85_3274) with
| (closing, bindings) -> begin
(let _177_2370 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((_177_2370), (bindings)))
end)))
in (match (_85_3277) with
| (q, bindings) -> begin
(

let _85_3286 = (let _177_2372 = (FStar_List.filter (fun _85_24 -> (match (_85_24) with
| FStar_TypeChecker_Env.Binding_sig (_85_3280) -> begin
false
end
| _85_3283 -> begin
true
end)) bindings)
in (encode_env_bindings env _177_2372))
in (match (_85_3286) with
| (env_decls, env) -> begin
(

let _85_3287 = if (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery")))) then begin
(let _177_2373 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _177_2373))
end else begin
()
end
in (

let _85_3291 = (encode_formula q env)
in (match (_85_3291) with
| (phi, qdecls) -> begin
(

let _85_3296 = (let _177_2374 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _177_2374 phi))
in (match (_85_3296) with
| (phi, labels, _85_3295) -> begin
(

let _85_3299 = (encode_labels labels)
in (match (_85_3299) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (let _177_2378 = (let _177_2377 = (FStar_SMTEncoding_Term.mkNot phi)
in (let _177_2376 = (let _177_2375 = (varops.fresh "@query")
in Some (_177_2375))
in ((_177_2377), (Some ("query")), (_177_2376))))
in FStar_SMTEncoding_Term.Assume (_177_2378))
in (

let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end))
end)))
end))
end))))))


let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (

let env = (get_env tcenv)
in (

let _85_3306 = (push "query")
in (

let _85_3311 = (encode_formula q env)
in (match (_85_3311) with
| (f, _85_3310) -> begin
(

let _85_3312 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _85_3316) -> begin
true
end
| _85_3320 -> begin
false
end))
end)))))






open Prims
# 32 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun x tl -> if (FStar_Options.unthrottle_inductives ()) then begin
tl
end else begin
(x)::tl
end)

# 34 "FStar.SMTEncoding.Encode.fst"
let withenv = (fun c _86_30 -> (match (_86_30) with
| (a, b) -> begin
((a), (b), (c))
end))

# 35 "FStar.SMTEncoding.Encode.fst"
let vargs = (fun args -> (FStar_List.filter (fun _86_1 -> (match (_86_1) with
| (FStar_Util.Inl (_86_34), _86_37) -> begin
false
end
| _86_40 -> begin
true
end)) args))

# 36 "FStar.SMTEncoding.Encode.fst"
let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l)) -> begin
(let _179_12 = (let _179_11 = (let _179_10 = (let _179_9 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _179_9))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _179_10))
in FStar_Util.Inl (_179_11))
in Some (_179_12))
end
| _86_47 -> begin
l
end))

# 39 "FStar.SMTEncoding.Encode.fst"
let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))

# 42 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (
# 44 "FStar.SMTEncoding.Encode.fst"
let a = (
# 44 "FStar.SMTEncoding.Encode.fst"
let _86_51 = a
in (let _179_19 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _179_19; FStar_Syntax_Syntax.index = _86_51.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _86_51.FStar_Syntax_Syntax.sort}))
in (let _179_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _179_20))))

# 45 "FStar.SMTEncoding.Encode.fst"
let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (
# 47 "FStar.SMTEncoding.Encode.fst"
let fail = (fun _86_58 -> (match (()) with
| () -> begin
(let _179_30 = (let _179_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _179_29 lid.FStar_Ident.str))
in (FStar_All.failwith _179_30))
end))
in (
# 48 "FStar.SMTEncoding.Encode.fst"
let _86_62 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_86_62) with
| (_86_60, t) -> begin
(match ((let _179_31 = (FStar_Syntax_Subst.compress t)
in _179_31.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 51 "FStar.SMTEncoding.Encode.fst"
let _86_70 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_86_70) with
| (binders, _86_69) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(
# 54 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end
end))
end
| _86_73 -> begin
(fail ())
end)
end))))

# 56 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _179_37 = (let _179_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _179_36))
in (FStar_All.pipe_left escape _179_37)))

# 57 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _179_43 = (let _179_42 = (mk_term_projector_name lid a)
in ((_179_42), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Term.mkFreeV _179_43)))

# 59 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _179_49 = (let _179_48 = (mk_term_projector_name_by_pos lid i)
in ((_179_48), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Term.mkFreeV _179_49)))

# 61 "FStar.SMTEncoding.Encode.fst"
let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

# 62 "FStar.SMTEncoding.Encode.fst"
type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}

# 65 "FStar.SMTEncoding.Encode.fst"
let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))

# 77 "FStar.SMTEncoding.Encode.fst"
let varops : varops_t = (
# 79 "FStar.SMTEncoding.Encode.fst"
let initial_ctr = 100
in (
# 80 "FStar.SMTEncoding.Encode.fst"
let ctr = (FStar_Util.mk_ref initial_ctr)
in (
# 81 "FStar.SMTEncoding.Encode.fst"
let new_scope = (fun _86_98 -> (match (()) with
| () -> begin
(let _179_162 = (FStar_Util.smap_create 100)
in (let _179_161 = (FStar_Util.smap_create 100)
in ((_179_162), (_179_161))))
end))
in (
# 82 "FStar.SMTEncoding.Encode.fst"
let scopes = (let _179_164 = (let _179_163 = (new_scope ())
in (_179_163)::[])
in (FStar_Util.mk_ref _179_164))
in (
# 83 "FStar.SMTEncoding.Encode.fst"
let mk_unique = (fun y -> (
# 84 "FStar.SMTEncoding.Encode.fst"
let y = (escape y)
in (
# 85 "FStar.SMTEncoding.Encode.fst"
let y = (match ((let _179_168 = (FStar_ST.read scopes)
in (FStar_Util.find_map _179_168 (fun _86_106 -> (match (_86_106) with
| (names, _86_105) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_86_109) -> begin
(
# 87 "FStar.SMTEncoding.Encode.fst"
let _86_111 = (FStar_Util.incr ctr)
in (let _179_171 = (let _179_170 = (let _179_169 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _179_169))
in (Prims.strcat "__" _179_170))
in (Prims.strcat y _179_171)))
end)
in (
# 88 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _179_173 = (let _179_172 = (FStar_ST.read scopes)
in (FStar_List.hd _179_172))
in (FStar_All.pipe_left Prims.fst _179_173))
in (
# 89 "FStar.SMTEncoding.Encode.fst"
let _86_115 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (
# 90 "FStar.SMTEncoding.Encode.fst"
let new_var = (fun pp rn -> (let _179_180 = (let _179_179 = (let _179_178 = (FStar_Util.string_of_int rn)
in (Prims.strcat "__" _179_178))
in (Prims.strcat pp.FStar_Ident.idText _179_179))
in (FStar_All.pipe_left mk_unique _179_180)))
in (
# 91 "FStar.SMTEncoding.Encode.fst"
let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (
# 92 "FStar.SMTEncoding.Encode.fst"
let next_id = (fun _86_123 -> (match (()) with
| () -> begin
(
# 92 "FStar.SMTEncoding.Encode.fst"
let _86_124 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (
# 93 "FStar.SMTEncoding.Encode.fst"
let fresh = (fun pfx -> (let _179_188 = (let _179_187 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _179_187))
in (FStar_Util.format2 "%s_%s" pfx _179_188)))
in (
# 94 "FStar.SMTEncoding.Encode.fst"
let string_const = (fun s -> (match ((let _179_192 = (FStar_ST.read scopes)
in (FStar_Util.find_map _179_192 (fun _86_133 -> (match (_86_133) with
| (_86_131, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(
# 97 "FStar.SMTEncoding.Encode.fst"
let id = (next_id ())
in (
# 98 "FStar.SMTEncoding.Encode.fst"
let f = (let _179_193 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _179_193))
in (
# 99 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _179_195 = (let _179_194 = (FStar_ST.read scopes)
in (FStar_List.hd _179_194))
in (FStar_All.pipe_left Prims.snd _179_195))
in (
# 100 "FStar.SMTEncoding.Encode.fst"
let _86_140 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (
# 102 "FStar.SMTEncoding.Encode.fst"
let push = (fun _86_143 -> (match (()) with
| () -> begin
(let _179_200 = (let _179_199 = (new_scope ())
in (let _179_198 = (FStar_ST.read scopes)
in (_179_199)::_179_198))
in (FStar_ST.op_Colon_Equals scopes _179_200))
end))
in (
# 103 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _86_145 -> (match (()) with
| () -> begin
(let _179_204 = (let _179_203 = (FStar_ST.read scopes)
in (FStar_List.tl _179_203))
in (FStar_ST.op_Colon_Equals scopes _179_204))
end))
in (
# 104 "FStar.SMTEncoding.Encode.fst"
let mark = (fun _86_147 -> (match (()) with
| () -> begin
(push ())
end))
in (
# 105 "FStar.SMTEncoding.Encode.fst"
let reset_mark = (fun _86_149 -> (match (()) with
| () -> begin
(pop ())
end))
in (
# 106 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun _86_151 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
(
# 108 "FStar.SMTEncoding.Encode.fst"
let _86_164 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (
# 109 "FStar.SMTEncoding.Encode.fst"
let _86_169 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes ((((next1), (next2)))::tl))))
end
| _86_172 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id; mk_unique = mk_unique})))))))))))))))

# 122 "FStar.SMTEncoding.Encode.fst"
let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (
# 124 "FStar.SMTEncoding.Encode.fst"
let _86_174 = x
in (let _179_219 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _179_219; FStar_Syntax_Syntax.index = _86_174.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _86_174.FStar_Syntax_Syntax.sort})))

# 124 "FStar.SMTEncoding.Encode.fst"
type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option)

# 129 "FStar.SMTEncoding.Encode.fst"
let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

# 130 "FStar.SMTEncoding.Encode.fst"
let is_Binding_fvar = (fun _discr_ -> (match (_discr_) with
| Binding_fvar (_) -> begin
true
end
| _ -> begin
false
end))

# 129 "FStar.SMTEncoding.Encode.fst"
let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_86_178) -> begin
_86_178
end))

# 130 "FStar.SMTEncoding.Encode.fst"
let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_86_181) -> begin
_86_181
end))

# 130 "FStar.SMTEncoding.Encode.fst"
let binder_of_eithervar = (fun v -> ((v), (None)))

# 133 "FStar.SMTEncoding.Encode.fst"
type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

# 134 "FStar.SMTEncoding.Encode.fst"
let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))

# 143 "FStar.SMTEncoding.Encode.fst"
let print_env : env_t  ->  Prims.string = (fun e -> (let _179_277 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _86_2 -> (match (_86_2) with
| Binding_var (x, _86_196) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _86_201, _86_203, _86_205) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _179_277 (FStar_String.concat ", "))))

# 147 "FStar.SMTEncoding.Encode.fst"
let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

# 149 "FStar.SMTEncoding.Encode.fst"
let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _179_287 = (FStar_Syntax_Print.term_to_string t)
in Some (_179_287))
end else begin
None
end)

# 154 "FStar.SMTEncoding.Encode.fst"
let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (
# 156 "FStar.SMTEncoding.Encode.fst"
let xsym = (varops.fresh x)
in (let _179_292 = (FStar_SMTEncoding_Term.mkFreeV ((xsym), (s)))
in ((xsym), (_179_292)))))

# 156 "FStar.SMTEncoding.Encode.fst"
let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 161 "FStar.SMTEncoding.Encode.fst"
let ysym = (let _179_297 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _179_297))
in (
# 162 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((
# 163 "FStar.SMTEncoding.Encode.fst"
let _86_219 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + 1); tcenv = _86_219.tcenv; warn = _86_219.warn; cache = _86_219.cache; nolabels = _86_219.nolabels; use_zfuel_name = _86_219.use_zfuel_name; encode_non_total_function_typ = _86_219.encode_non_total_function_typ}))))))

# 163 "FStar.SMTEncoding.Encode.fst"
let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 165 "FStar.SMTEncoding.Encode.fst"
let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (
# 166 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkApp ((ysym), ([])))
in ((ysym), (y), ((
# 167 "FStar.SMTEncoding.Encode.fst"
let _86_225 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _86_225.depth; tcenv = _86_225.tcenv; warn = _86_225.warn; cache = _86_225.cache; nolabels = _86_225.nolabels; use_zfuel_name = _86_225.use_zfuel_name; encode_non_total_function_typ = _86_225.encode_non_total_function_typ}))))))

# 167 "FStar.SMTEncoding.Encode.fst"
let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (
# 169 "FStar.SMTEncoding.Encode.fst"
let ysym = (varops.mk_unique str)
in (
# 170 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkApp ((ysym), ([])))
in ((ysym), (y), ((
# 171 "FStar.SMTEncoding.Encode.fst"
let _86_232 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = _86_232.depth; tcenv = _86_232.tcenv; warn = _86_232.warn; cache = _86_232.cache; nolabels = _86_232.nolabels; use_zfuel_name = _86_232.use_zfuel_name; encode_non_total_function_typ = _86_232.encode_non_total_function_typ}))))))

# 171 "FStar.SMTEncoding.Encode.fst"
let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (
# 173 "FStar.SMTEncoding.Encode.fst"
let _86_237 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = _86_237.depth; tcenv = _86_237.tcenv; warn = _86_237.warn; cache = _86_237.cache; nolabels = _86_237.nolabels; use_zfuel_name = _86_237.use_zfuel_name; encode_non_total_function_typ = _86_237.encode_non_total_function_typ}))

# 173 "FStar.SMTEncoding.Encode.fst"
let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (
# 175 "FStar.SMTEncoding.Encode.fst"
let aux = (fun a' -> (lookup_binding env (fun _86_3 -> (match (_86_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some (((b), (t)))
end
| _86_249 -> begin
None
end))))
in (match ((aux a)) with
| None -> begin
(
# 179 "FStar.SMTEncoding.Encode.fst"
let a = (unmangle a)
in (match ((aux a)) with
| None -> begin
(let _179_322 = (let _179_321 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found (after unmangling): %s" _179_321))
in (FStar_All.failwith _179_322))
end
| Some (b, t) -> begin
t
end))
end
| Some (b, t) -> begin
t
end)))

# 183 "FStar.SMTEncoding.Encode.fst"
let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (
# 187 "FStar.SMTEncoding.Encode.fst"
let fname = (varops.new_fvar x)
in (
# 188 "FStar.SMTEncoding.Encode.fst"
let ftok = (Prims.strcat fname "@tok")
in (let _179_333 = (
# 190 "FStar.SMTEncoding.Encode.fst"
let _86_265 = env
in (let _179_332 = (let _179_331 = (let _179_330 = (let _179_329 = (let _179_328 = (FStar_SMTEncoding_Term.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _179_327 -> Some (_179_327)) _179_328))
in ((x), (fname), (_179_329), (None)))
in Binding_fvar (_179_330))
in (_179_331)::env.bindings)
in {bindings = _179_332; depth = _86_265.depth; tcenv = _86_265.tcenv; warn = _86_265.warn; cache = _86_265.cache; nolabels = _86_265.nolabels; use_zfuel_name = _86_265.use_zfuel_name; encode_non_total_function_typ = _86_265.encode_non_total_function_typ}))
in ((fname), (ftok), (_179_333))))))

# 190 "FStar.SMTEncoding.Encode.fst"
let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _86_4 -> (match (_86_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| _86_277 -> begin
None
end))))

# 192 "FStar.SMTEncoding.Encode.fst"
let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (let _179_344 = (lookup_binding env (fun _86_5 -> (match (_86_5) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| _86_288 -> begin
None
end)))
in (FStar_All.pipe_right _179_344 FStar_Option.isSome)))

# 194 "FStar.SMTEncoding.Encode.fst"
let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _179_350 = (let _179_349 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _179_349))
in (FStar_All.failwith _179_350))
end
| Some (s) -> begin
s
end))

# 198 "FStar.SMTEncoding.Encode.fst"
let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (
# 200 "FStar.SMTEncoding.Encode.fst"
let _86_298 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = _86_298.depth; tcenv = _86_298.tcenv; warn = _86_298.warn; cache = _86_298.cache; nolabels = _86_298.nolabels; use_zfuel_name = _86_298.use_zfuel_name; encode_non_total_function_typ = _86_298.encode_non_total_function_typ}))

# 200 "FStar.SMTEncoding.Encode.fst"
let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (
# 202 "FStar.SMTEncoding.Encode.fst"
let _86_307 = (lookup_lid env x)
in (match (_86_307) with
| (t1, t2, _86_306) -> begin
(
# 203 "FStar.SMTEncoding.Encode.fst"
let t3 = (let _179_367 = (let _179_366 = (let _179_365 = (FStar_SMTEncoding_Term.mkApp (("ZFuel"), ([])))
in (_179_365)::[])
in ((f), (_179_366)))
in (FStar_SMTEncoding_Term.mkApp _179_367))
in (
# 204 "FStar.SMTEncoding.Encode.fst"
let _86_309 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = _86_309.depth; tcenv = _86_309.tcenv; warn = _86_309.warn; cache = _86_309.cache; nolabels = _86_309.nolabels; use_zfuel_name = _86_309.use_zfuel_name; encode_non_total_function_typ = _86_309.encode_non_total_function_typ}))
end)))

# 204 "FStar.SMTEncoding.Encode.fst"
let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
None
end
| Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
Some (f)
end
| _86_322 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_86_326, (fuel)::[]) -> begin
if (let _179_373 = (let _179_372 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _179_372 Prims.fst))
in (FStar_Util.starts_with _179_373 "fuel")) then begin
(let _179_376 = (let _179_375 = (FStar_SMTEncoding_Term.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF _179_375 fuel))
in (FStar_All.pipe_left (fun _179_374 -> Some (_179_374)) _179_376))
end else begin
Some (t)
end
end
| _86_332 -> begin
Some (t)
end)
end
| _86_334 -> begin
None
end)
end)
end))

# 221 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _179_380 = (let _179_379 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _179_379))
in (FStar_All.failwith _179_380))
end))

# 225 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_name = (fun env a -> (
# 226 "FStar.SMTEncoding.Encode.fst"
let _86_347 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_86_347) with
| (x, _86_344, _86_346) -> begin
x
end)))

# 226 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_sym = (fun env a -> (
# 228 "FStar.SMTEncoding.Encode.fst"
let _86_353 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_86_353) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _86_357; FStar_SMTEncoding_Term.freevars = _86_355}) when env.use_zfuel_name -> begin
((g), (zf))
end
| _86_365 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| _86_375 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))

# 237 "FStar.SMTEncoding.Encode.fst"
let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _86_6 -> (match (_86_6) with
| Binding_fvar (_86_380, nm', tok, _86_384) when (nm = nm') -> begin
tok
end
| _86_388 -> begin
None
end))))

# 242 "FStar.SMTEncoding.Encode.fst"
let mkForall_fuel' = (fun n _86_393 -> (match (_86_393) with
| (pats, vars, body) -> begin
(
# 249 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _86_395 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall ((pats), (vars), (body)))
end))
in if (FStar_Options.unthrottle_inductives ()) then begin
(fallback ())
end else begin
(
# 252 "FStar.SMTEncoding.Encode.fst"
let _86_398 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_86_398) with
| (fsym, fterm) -> begin
(
# 253 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| _86_408 -> begin
p
end)))))
in (
# 257 "FStar.SMTEncoding.Encode.fst"
let pats = (FStar_List.map add_fuel pats)
in (
# 258 "FStar.SMTEncoding.Encode.fst"
let body = (match (body.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (guard)::(body')::[]) -> begin
(
# 260 "FStar.SMTEncoding.Encode.fst"
let guard = (match (guard.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, guards) -> begin
(let _179_397 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _179_397))
end
| _86_421 -> begin
(let _179_398 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _179_398 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp ((guard), (body'))))
end
| _86_424 -> begin
body
end)
in (
# 265 "FStar.SMTEncoding.Encode.fst"
let vars = (((fsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars
in (FStar_SMTEncoding_Term.mkForall ((pats), (vars), (body)))))))
end))
end)
end))

# 266 "FStar.SMTEncoding.Encode.fst"
let mkForall_fuel : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' 1)

# 268 "FStar.SMTEncoding.Encode.fst"
let head_normal : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (
# 271 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_fvar (fv)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _179_404 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _179_404 FStar_Option.isNone))
end
| _86_463 -> begin
false
end)))

# 281 "FStar.SMTEncoding.Encode.fst"
let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (match ((let _179_409 = (FStar_Syntax_Util.un_uinst t)
in _179_409.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (_86_467) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(let _179_410 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _179_410 FStar_Option.isSome))
end
| _86_472 -> begin
false
end))

# 286 "FStar.SMTEncoding.Encode.fst"
let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)

# 290 "FStar.SMTEncoding.Encode.fst"
let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))

# 291 "FStar.SMTEncoding.Encode.fst"
let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _179_423 = (let _179_421 = (FStar_Syntax_Syntax.null_binder t)
in (_179_421)::[])
in (let _179_422 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _179_423 _179_422 None))))

# 296 "FStar.SMTEncoding.Encode.fst"
let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _179_430 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _179_430))
end
| s -> begin
(
# 301 "FStar.SMTEncoding.Encode.fst"
let _86_484 = ()
in (let _179_431 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _179_431)))
end)) e)))

# 301 "FStar.SMTEncoding.Encode.fst"
let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))

# 302 "FStar.SMTEncoding.Encode.fst"
let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _86_7 -> (match (_86_7) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _86_494 -> begin
false
end))

# 307 "FStar.SMTEncoding.Encode.fst"
let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (
# 310 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _86_505; FStar_SMTEncoding_Term.freevars = _86_503})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _86_523) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _86_530 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_86_532, []) -> begin
(
# 321 "FStar.SMTEncoding.Encode.fst"
let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _86_538 -> begin
None
end))
in (aux t (FStar_List.rev vars))))

# 326 "FStar.SMTEncoding.Encode.fst"
type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)

# 352 "FStar.SMTEncoding.Encode.fst"
type labels =
label Prims.list

# 353 "FStar.SMTEncoding.Encode.fst"
type pattern =
{pat_vars : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t); guard : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term; projections : FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list}

# 354 "FStar.SMTEncoding.Encode.fst"
let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))

# 360 "FStar.SMTEncoding.Encode.fst"
exception Let_rec_unencodeable

# 360 "FStar.SMTEncoding.Encode.fst"
let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable (_) -> begin
true
end
| _ -> begin
false
end))

# 360 "FStar.SMTEncoding.Encode.fst"
let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _86_8 -> (match (_86_8) with
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
(let _179_488 = (let _179_487 = (let _179_486 = (let _179_485 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _179_485))
in (_179_486)::[])
in (("FStar.Char.Char"), (_179_487)))
in (FStar_SMTEncoding_Term.mkApp _179_488))
end
| FStar_Const.Const_int (i, None) -> begin
(let _179_489 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _179_489))
end
| FStar_Const.Const_int (i, Some (_86_558)) -> begin
(FStar_All.failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, _86_564) -> begin
(let _179_490 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _179_490))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _179_492 = (let _179_491 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _179_491))
in (FStar_All.failwith _179_492))
end))

# 372 "FStar.SMTEncoding.Encode.fst"
let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (
# 375 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t -> (
# 376 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_86_578) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_86_581) -> begin
(let _179_501 = (FStar_Syntax_Util.unrefine t)
in (aux true _179_501))
end
| _86_584 -> begin
if norm then begin
(let _179_502 = (whnf env t)
in (aux false _179_502))
end else begin
(let _179_505 = (let _179_504 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _179_503 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _179_504 _179_503)))
in (FStar_All.failwith _179_505))
end
end)))
in (aux true t0)))

# 383 "FStar.SMTEncoding.Encode.fst"
let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (
# 386 "FStar.SMTEncoding.Encode.fst"
let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _86_592 -> begin
(let _179_508 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (_179_508)))
end)))

# 389 "FStar.SMTEncoding.Encode.fst"
let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (
# 399 "FStar.SMTEncoding.Encode.fst"
let _86_596 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _179_556 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _179_556))
end else begin
()
end
in (
# 401 "FStar.SMTEncoding.Encode.fst"
let _86_624 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _86_603 b -> (match (_86_603) with
| (vars, guards, env, decls, names) -> begin
(
# 402 "FStar.SMTEncoding.Encode.fst"
let _86_618 = (
# 403 "FStar.SMTEncoding.Encode.fst"
let x = (unmangle (Prims.fst b))
in (
# 404 "FStar.SMTEncoding.Encode.fst"
let _86_609 = (gen_term_var env x)
in (match (_86_609) with
| (xxsym, xx, env') -> begin
(
# 405 "FStar.SMTEncoding.Encode.fst"
let _86_612 = (let _179_559 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _179_559 env xx))
in (match (_86_612) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (_86_618) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (_86_624) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 420 "FStar.SMTEncoding.Encode.fst"
let _86_631 = (encode_term t env)
in (match (_86_631) with
| (t, decls) -> begin
(let _179_564 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((_179_564), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 424 "FStar.SMTEncoding.Encode.fst"
let _86_638 = (encode_term t env)
in (match (_86_638) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _179_569 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((_179_569), (decls)))
end
| Some (f) -> begin
(let _179_570 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((_179_570), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (
# 432 "FStar.SMTEncoding.Encode.fst"
let t0 = (FStar_Syntax_Subst.compress t)
in (
# 433 "FStar.SMTEncoding.Encode.fst"
let _86_645 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _179_575 = (FStar_Syntax_Print.tag_of_term t)
in (let _179_574 = (FStar_Syntax_Print.tag_of_term t0)
in (let _179_573 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _179_575 _179_574 _179_573))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _179_580 = (let _179_579 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _179_578 = (FStar_Syntax_Print.tag_of_term t0)
in (let _179_577 = (FStar_Syntax_Print.term_to_string t0)
in (let _179_576 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _179_579 _179_578 _179_577 _179_576)))))
in (FStar_All.failwith _179_580))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _179_582 = (let _179_581 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _179_581))
in (FStar_All.failwith _179_582))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _86_656) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _86_661) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 449 "FStar.SMTEncoding.Encode.fst"
let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _179_583 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((_179_583), ([])))
end
| FStar_Syntax_Syntax.Tm_type (_86_670) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, _86_674) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _179_584 = (encode_const c)
in ((_179_584), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 465 "FStar.SMTEncoding.Encode.fst"
let _86_685 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_86_685) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(
# 469 "FStar.SMTEncoding.Encode.fst"
let _86_692 = (encode_binders None binders env)
in (match (_86_692) with
| (vars, guards, env', decls, _86_691) -> begin
(
# 470 "FStar.SMTEncoding.Encode.fst"
let fsym = (let _179_585 = (varops.fresh "f")
in ((_179_585), (FStar_SMTEncoding_Term.Term_sort)))
in (
# 471 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 472 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 473 "FStar.SMTEncoding.Encode.fst"
let _86_700 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (
# 473 "FStar.SMTEncoding.Encode.fst"
let _86_696 = env.tcenv
in {FStar_TypeChecker_Env.solver = _86_696.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _86_696.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _86_696.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _86_696.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _86_696.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _86_696.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _86_696.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _86_696.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _86_696.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _86_696.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _86_696.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _86_696.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _86_696.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _86_696.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _86_696.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _86_696.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _86_696.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _86_696.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _86_696.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _86_696.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _86_696.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _86_696.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (_86_700) with
| (pre_opt, res_t) -> begin
(
# 474 "FStar.SMTEncoding.Encode.fst"
let _86_703 = (encode_term_pred None res_t env' app)
in (match (_86_703) with
| (res_pred, decls') -> begin
(
# 475 "FStar.SMTEncoding.Encode.fst"
let _86_712 = (match (pre_opt) with
| None -> begin
(let _179_586 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_179_586), ([])))
end
| Some (pre) -> begin
(
# 478 "FStar.SMTEncoding.Encode.fst"
let _86_709 = (encode_formula pre env')
in (match (_86_709) with
| (guard, decls0) -> begin
(let _179_587 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in ((_179_587), (decls0)))
end))
end)
in (match (_86_712) with
| (guards, guard_decls) -> begin
(
# 480 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _179_589 = (let _179_588 = (FStar_SMTEncoding_Term.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (_179_588)))
in (FStar_SMTEncoding_Term.mkForall _179_589))
in (
# 485 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _179_591 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _179_591 (FStar_List.filter (fun _86_717 -> (match (_86_717) with
| (x, _86_716) -> begin
(x <> (Prims.fst fsym))
end)))))
in (
# 486 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _86_723) -> begin
(let _179_594 = (let _179_593 = (let _179_592 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((t'), (_179_592)))
in (FStar_SMTEncoding_Term.mkApp _179_593))
in ((_179_594), ([])))
end
| None -> begin
(
# 492 "FStar.SMTEncoding.Encode.fst"
let tsym = (let _179_596 = (let _179_595 = (FStar_Util.digest_of_string tkey.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "Tm_arrow_" _179_595))
in (varops.mk_unique _179_596))
in (
# 493 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 494 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_Options.log_queries ()) then begin
(let _179_597 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_179_597))
end else begin
None
end
in (
# 499 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (
# 501 "FStar.SMTEncoding.Encode.fst"
let t = (let _179_599 = (let _179_598 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((tsym), (_179_598)))
in (FStar_SMTEncoding_Term.mkApp _179_599))
in (
# 502 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 504 "FStar.SMTEncoding.Encode.fst"
let k_assumption = (
# 505 "FStar.SMTEncoding.Encode.fst"
let a_name = Some ((Prims.strcat "kinding_" tsym))
in (let _179_601 = (let _179_600 = (FStar_SMTEncoding_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_179_600), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_179_601)))
in (
# 508 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 509 "FStar.SMTEncoding.Encode.fst"
let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (
# 510 "FStar.SMTEncoding.Encode.fst"
let pre_typing = (
# 511 "FStar.SMTEncoding.Encode.fst"
let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _179_608 = (let _179_607 = (let _179_606 = (let _179_605 = (let _179_604 = (let _179_603 = (let _179_602 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _179_602))
in ((f_has_t), (_179_603)))
in (FStar_SMTEncoding_Term.mkImp _179_604))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (_179_605)))
in (mkForall_fuel _179_606))
in ((_179_607), (Some ("pre-typing for functions")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_179_608)))
in (
# 513 "FStar.SMTEncoding.Encode.fst"
let t_interp = (
# 514 "FStar.SMTEncoding.Encode.fst"
let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (let _179_612 = (let _179_611 = (let _179_610 = (let _179_609 = (FStar_SMTEncoding_Term.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (_179_609)))
in (FStar_SMTEncoding_Term.mkForall _179_610))
in ((_179_611), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_179_612)))
in (
# 517 "FStar.SMTEncoding.Encode.fst"
let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp)::[]))))
in (
# 518 "FStar.SMTEncoding.Encode.fst"
let _86_742 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((tsym), (cvar_sorts), (t_decls)))
in ((t), (t_decls)))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(
# 522 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Non_total_Tm_arrow")
in (
# 523 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (
# 524 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_SMTEncoding_Term.mkApp ((tsym), ([])))
in (
# 525 "FStar.SMTEncoding.Encode.fst"
let t_kinding = (
# 526 "FStar.SMTEncoding.Encode.fst"
let a_name = Some ((Prims.strcat "non_total_function_typing_" tsym))
in (let _179_614 = (let _179_613 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((_179_613), (Some ("Typing for non-total arrows")), (a_name)))
in FStar_SMTEncoding_Term.Assume (_179_614)))
in (
# 528 "FStar.SMTEncoding.Encode.fst"
let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 529 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 530 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 531 "FStar.SMTEncoding.Encode.fst"
let t_interp = (
# 532 "FStar.SMTEncoding.Encode.fst"
let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (let _179_621 = (let _179_620 = (let _179_619 = (let _179_618 = (let _179_617 = (let _179_616 = (let _179_615 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _179_615))
in ((f_has_t), (_179_616)))
in (FStar_SMTEncoding_Term.mkImp _179_617))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (_179_618)))
in (mkForall_fuel _179_619))
in ((_179_620), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_179_621)))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_86_755) -> begin
(
# 541 "FStar.SMTEncoding.Encode.fst"
let _86_775 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _86_762; FStar_Syntax_Syntax.pos = _86_760; FStar_Syntax_Syntax.vars = _86_758} -> begin
(
# 543 "FStar.SMTEncoding.Encode.fst"
let _86_770 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (_86_770) with
| (b, f) -> begin
(let _179_623 = (let _179_622 = (FStar_List.hd b)
in (Prims.fst _179_622))
in ((_179_623), (f)))
end))
end
| _86_772 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_86_775) with
| (x, f) -> begin
(
# 547 "FStar.SMTEncoding.Encode.fst"
let _86_778 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_86_778) with
| (base_t, decls) -> begin
(
# 548 "FStar.SMTEncoding.Encode.fst"
let _86_782 = (gen_term_var env x)
in (match (_86_782) with
| (x, xtm, env') -> begin
(
# 549 "FStar.SMTEncoding.Encode.fst"
let _86_785 = (encode_formula f env')
in (match (_86_785) with
| (refinement, decls') -> begin
(
# 551 "FStar.SMTEncoding.Encode.fst"
let _86_788 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_86_788) with
| (fsym, fterm) -> begin
(
# 553 "FStar.SMTEncoding.Encode.fst"
let encoding = (let _179_625 = (let _179_624 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((_179_624), (refinement)))
in (FStar_SMTEncoding_Term.mkAnd _179_625))
in (
# 555 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _179_627 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _179_627 (FStar_List.filter (fun _86_793 -> (match (_86_793) with
| (y, _86_792) -> begin
((y <> x) && (y <> fsym))
end)))))
in (
# 556 "FStar.SMTEncoding.Encode.fst"
let xfv = ((x), (FStar_SMTEncoding_Term.Term_sort))
in (
# 557 "FStar.SMTEncoding.Encode.fst"
let ffv = ((fsym), (FStar_SMTEncoding_Term.Fuel_sort))
in (
# 558 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall (([]), ((ffv)::(xfv)::cvars), (encoding)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _86_800, _86_802) -> begin
(let _179_630 = (let _179_629 = (let _179_628 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in ((t), (_179_628)))
in (FStar_SMTEncoding_Term.mkApp _179_629))
in ((_179_630), ([])))
end
| None -> begin
(
# 565 "FStar.SMTEncoding.Encode.fst"
let tsym = (let _179_632 = (let _179_631 = (FStar_Util.digest_of_string tkey.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "Tm_refine_" _179_631))
in (varops.mk_unique _179_632))
in (
# 566 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 567 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (
# 568 "FStar.SMTEncoding.Encode.fst"
let t = (let _179_634 = (let _179_633 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((tsym), (_179_633)))
in (FStar_SMTEncoding_Term.mkApp _179_634))
in (
# 570 "FStar.SMTEncoding.Encode.fst"
let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (
# 571 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 574 "FStar.SMTEncoding.Encode.fst"
let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (
# 575 "FStar.SMTEncoding.Encode.fst"
let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t)
in (
# 577 "FStar.SMTEncoding.Encode.fst"
let t_haseq = (let _179_638 = (let _179_637 = (let _179_636 = (let _179_635 = (FStar_SMTEncoding_Term.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (_179_635)))
in (FStar_SMTEncoding_Term.mkForall _179_636))
in ((_179_637), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym)))))
in FStar_SMTEncoding_Term.Assume (_179_638))
in (
# 580 "FStar.SMTEncoding.Encode.fst"
let t_kinding = (let _179_640 = (let _179_639 = (FStar_SMTEncoding_Term.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((_179_639), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym)))))
in FStar_SMTEncoding_Term.Assume (_179_640))
in (
# 583 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _179_646 = (let _179_645 = (let _179_642 = (let _179_641 = (FStar_SMTEncoding_Term.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (_179_641)))
in (FStar_SMTEncoding_Term.mkForall _179_642))
in (let _179_644 = (let _179_643 = (FStar_Syntax_Print.term_to_string t0)
in Some (_179_643))
in ((_179_645), (_179_644), (Some ((Prims.strcat "refinement_interpretation_" tsym))))))
in FStar_SMTEncoding_Term.Assume (_179_646))
in (
# 587 "FStar.SMTEncoding.Encode.fst"
let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq)::[])))
in (
# 592 "FStar.SMTEncoding.Encode.fst"
let _86_818 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((tsym), (cvar_sorts), (t_decls)))
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
# 597 "FStar.SMTEncoding.Encode.fst"
let ttm = (let _179_647 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _179_647))
in (
# 598 "FStar.SMTEncoding.Encode.fst"
let _86_827 = (encode_term_pred None k env ttm)
in (match (_86_827) with
| (t_has_k, decls) -> begin
(
# 599 "FStar.SMTEncoding.Encode.fst"
let d = (let _179_653 = (let _179_652 = (let _179_651 = (let _179_650 = (let _179_649 = (let _179_648 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int _179_648))
in (FStar_Util.format1 "uvar_typing_%s" _179_649))
in (varops.mk_unique _179_650))
in Some (_179_651))
in ((t_has_k), (Some ("Uvar typing")), (_179_652)))
in FStar_SMTEncoding_Term.Assume (_179_653))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_86_830) -> begin
(
# 603 "FStar.SMTEncoding.Encode.fst"
let _86_834 = (FStar_Syntax_Util.head_and_args t0)
in (match (_86_834) with
| (head, args_e) -> begin
(match ((let _179_655 = (let _179_654 = (FStar_Syntax_Subst.compress head)
in _179_654.FStar_Syntax_Syntax.n)
in ((_179_655), (args_e)))) with
| (_86_836, _86_838) when (head_redex env head) -> begin
(let _179_656 = (whnf env t)
in (encode_term _179_656 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(
# 612 "FStar.SMTEncoding.Encode.fst"
let _86_878 = (encode_term v1 env)
in (match (_86_878) with
| (v1, decls1) -> begin
(
# 613 "FStar.SMTEncoding.Encode.fst"
let _86_881 = (encode_term v2 env)
in (match (_86_881) with
| (v2, decls2) -> begin
(let _179_657 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in ((_179_657), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), (_86_890)::(_86_887)::_86_885) -> begin
(
# 617 "FStar.SMTEncoding.Encode.fst"
let e0 = (let _179_661 = (let _179_660 = (let _179_659 = (let _179_658 = (FStar_List.hd args_e)
in (_179_658)::[])
in ((head), (_179_659)))
in FStar_Syntax_Syntax.Tm_app (_179_660))
in (FStar_Syntax_Syntax.mk _179_661 None head.FStar_Syntax_Syntax.pos))
in (
# 618 "FStar.SMTEncoding.Encode.fst"
let e = (let _179_664 = (let _179_663 = (let _179_662 = (FStar_List.tl args_e)
in ((e0), (_179_662)))
in FStar_Syntax_Syntax.Tm_app (_179_663))
in (FStar_Syntax_Syntax.mk _179_664 None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env)))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), ((arg, _86_899))::[]) -> begin
(
# 622 "FStar.SMTEncoding.Encode.fst"
let _86_905 = (encode_term arg env)
in (match (_86_905) with
| (tm, decls) -> begin
(let _179_665 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Var ("Reify")), ((tm)::[])))))
in ((_179_665), (decls)))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (_86_907)), ((arg, _86_912))::[]) -> begin
(encode_term arg env)
end
| _86_917 -> begin
(
# 629 "FStar.SMTEncoding.Encode.fst"
let _86_920 = (encode_args args_e env)
in (match (_86_920) with
| (args, decls) -> begin
(
# 631 "FStar.SMTEncoding.Encode.fst"
let encode_partial_app = (fun ht_opt -> (
# 632 "FStar.SMTEncoding.Encode.fst"
let _86_925 = (encode_term head env)
in (match (_86_925) with
| (head, decls') -> begin
(
# 633 "FStar.SMTEncoding.Encode.fst"
let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(
# 637 "FStar.SMTEncoding.Encode.fst"
let _86_934 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_86_934) with
| (formals, rest) -> begin
(
# 638 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _86_938 _86_942 -> (match (((_86_938), (_86_942))) with
| ((bv, _86_937), (a, _86_941)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (
# 639 "FStar.SMTEncoding.Encode.fst"
let ty = (let _179_670 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _179_670 (FStar_Syntax_Subst.subst subst)))
in (
# 640 "FStar.SMTEncoding.Encode.fst"
let _86_947 = (encode_term_pred None ty env app_tm)
in (match (_86_947) with
| (has_type, decls'') -> begin
(
# 641 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (
# 642 "FStar.SMTEncoding.Encode.fst"
let e_typing = (let _179_676 = (let _179_675 = (FStar_SMTEncoding_Term.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (let _179_674 = (let _179_673 = (let _179_672 = (let _179_671 = (FStar_Util.digest_of_string app_tm.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "partial_app_typing_" _179_671))
in (varops.mk_unique _179_672))
in Some (_179_673))
in ((_179_675), (Some ("Partial app typing")), (_179_674))))
in FStar_SMTEncoding_Term.Assume (_179_676))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (
# 648 "FStar.SMTEncoding.Encode.fst"
let encode_full_app = (fun fv -> (
# 649 "FStar.SMTEncoding.Encode.fst"
let _86_954 = (lookup_free_var_sym env fv)
in (match (_86_954) with
| (fname, fuel_args) -> begin
(
# 650 "FStar.SMTEncoding.Encode.fst"
let tm = (FStar_SMTEncoding_Term.mkApp' ((fname), ((FStar_List.append fuel_args args))))
in ((tm), (decls)))
end)))
in (
# 653 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Subst.compress head)
in (
# 655 "FStar.SMTEncoding.Encode.fst"
let head_type = (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
Some (x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(let _179_680 = (let _179_679 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _179_679 Prims.snd))
in Some (_179_680))
end
| FStar_Syntax_Syntax.Tm_ascribed (_86_986, FStar_Util.Inl (t), _86_990) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (_86_994, FStar_Util.Inr (c), _86_998) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| _86_1002 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(
# 667 "FStar.SMTEncoding.Encode.fst"
let head_type = (let _179_681 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _179_681))
in (
# 668 "FStar.SMTEncoding.Encode.fst"
let _86_1010 = (curried_arrow_formals_comp head_type)
in (match (_86_1010) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _86_1026 -> begin
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
# 682 "FStar.SMTEncoding.Encode.fst"
let _86_1035 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_86_1035) with
| (bs, body, opening) -> begin
(
# 683 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _86_1037 -> (match (()) with
| () -> begin
(
# 684 "FStar.SMTEncoding.Encode.fst"
let f = (varops.fresh "Tm_abs")
in (
# 685 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (let _179_684 = (FStar_SMTEncoding_Term.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((_179_684), ((decl)::[])))))
end))
in (
# 689 "FStar.SMTEncoding.Encode.fst"
let is_impure = (fun _86_9 -> (match (_86_9) with
| FStar_Util.Inl (lc) -> begin
(not ((FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)))
end
| FStar_Util.Inr (eff) -> begin
(let _179_687 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right _179_687 Prims.op_Negation))
end))
in (
# 694 "FStar.SMTEncoding.Encode.fst"
let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(let _179_692 = (let _179_690 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening _179_690))
in (FStar_All.pipe_right _179_692 (fun _179_691 -> Some (_179_691))))
end
| FStar_Util.Inr (eff) -> begin
(
# 697 "FStar.SMTEncoding.Encode.fst"
let new_uvar = (fun _86_1053 -> (match (()) with
| () -> begin
(let _179_695 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right _179_695 Prims.fst))
end))
in if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) then begin
(let _179_698 = (let _179_696 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total _179_696))
in (FStar_All.pipe_right _179_698 (fun _179_697 -> Some (_179_697))))
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) then begin
(let _179_701 = (let _179_699 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal _179_699))
in (FStar_All.pipe_right _179_701 (fun _179_700 -> Some (_179_700))))
end else begin
None
end
end)
end))
in (match (lopt) with
| None -> begin
(
# 707 "FStar.SMTEncoding.Encode.fst"
let _86_1055 = (let _179_703 = (let _179_702 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _179_702))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _179_703))
in (fallback ()))
end
| Some (lc) -> begin
if (is_impure lc) then begin
(fallback ())
end else begin
(
# 713 "FStar.SMTEncoding.Encode.fst"
let _86_1065 = (encode_binders None bs env)
in (match (_86_1065) with
| (vars, guards, envbody, decls, _86_1064) -> begin
(
# 714 "FStar.SMTEncoding.Encode.fst"
let _86_1068 = (encode_term body envbody)
in (match (_86_1068) with
| (body, decls') -> begin
(
# 715 "FStar.SMTEncoding.Encode.fst"
let key_body = (let _179_707 = (let _179_706 = (let _179_705 = (let _179_704 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_179_704), (body)))
in (FStar_SMTEncoding_Term.mkImp _179_705))
in (([]), (vars), (_179_706)))
in (FStar_SMTEncoding_Term.mkForall _179_707))
in (
# 716 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (
# 717 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall (([]), (cvars), (key_body)))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _86_1074, _86_1076) -> begin
(let _179_710 = (let _179_709 = (let _179_708 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((t), (_179_708)))
in (FStar_SMTEncoding_Term.mkApp _179_709))
in ((_179_710), ([])))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
((t), ([]))
end
| None -> begin
(
# 724 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 725 "FStar.SMTEncoding.Encode.fst"
let fsym = (let _179_712 = (let _179_711 = (FStar_Util.digest_of_string tkey.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "Tm_abs_" _179_711))
in (varops.mk_unique _179_712))
in (
# 726 "FStar.SMTEncoding.Encode.fst"
let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (
# 727 "FStar.SMTEncoding.Encode.fst"
let f = (let _179_714 = (let _179_713 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in ((fsym), (_179_713)))
in (FStar_SMTEncoding_Term.mkApp _179_714))
in (
# 728 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 729 "FStar.SMTEncoding.Encode.fst"
let typing_f = (match ((codomain_eff lc)) with
| None -> begin
[]
end
| Some (c) -> begin
(
# 733 "FStar.SMTEncoding.Encode.fst"
let tfun = (FStar_Syntax_Util.arrow bs c)
in (
# 734 "FStar.SMTEncoding.Encode.fst"
let _86_1094 = (encode_term_pred None tfun env f)
in (match (_86_1094) with
| (f_has_t, decls'') -> begin
(
# 735 "FStar.SMTEncoding.Encode.fst"
let a_name = Some ((Prims.strcat "typing_" fsym))
in (let _179_718 = (let _179_717 = (let _179_716 = (let _179_715 = (FStar_SMTEncoding_Term.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((_179_715), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_179_716))
in (_179_717)::[])
in (FStar_List.append decls'' _179_718)))
end)))
end)
in (
# 737 "FStar.SMTEncoding.Encode.fst"
let interp_f = (
# 738 "FStar.SMTEncoding.Encode.fst"
let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (let _179_722 = (let _179_721 = (let _179_720 = (let _179_719 = (FStar_SMTEncoding_Term.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (_179_719)))
in (FStar_SMTEncoding_Term.mkForall _179_720))
in ((_179_721), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (_179_722)))
in (
# 740 "FStar.SMTEncoding.Encode.fst"
let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[]))))
in (
# 741 "FStar.SMTEncoding.Encode.fst"
let _86_1100 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash ((fsym), (cvar_sorts), (f_decls)))
in ((f), (f_decls)))))))))))
end)
end))))
end))
end))
end
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_86_1103, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_86_1115); FStar_Syntax_Syntax.lbunivs = _86_1113; FStar_Syntax_Syntax.lbtyp = _86_1111; FStar_Syntax_Syntax.lbeff = _86_1109; FStar_Syntax_Syntax.lbdef = _86_1107})::_86_1105), _86_1121) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _86_1130; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _86_1127; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_86_1140) -> begin
(
# 752 "FStar.SMTEncoding.Encode.fst"
let _86_1142 = (FStar_TypeChecker_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (
# 753 "FStar.SMTEncoding.Encode.fst"
let e = (varops.fresh "let-rec")
in (
# 754 "FStar.SMTEncoding.Encode.fst"
let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (let _179_723 = (FStar_SMTEncoding_Term.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((_179_723), ((decl_e)::[]))))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (
# 761 "FStar.SMTEncoding.Encode.fst"
let _86_1158 = (encode_term e1 env)
in (match (_86_1158) with
| (ee1, decls1) -> begin
(
# 762 "FStar.SMTEncoding.Encode.fst"
let _86_1161 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (_86_1161) with
| (xs, e2) -> begin
(
# 763 "FStar.SMTEncoding.Encode.fst"
let _86_1165 = (FStar_List.hd xs)
in (match (_86_1165) with
| (x, _86_1164) -> begin
(
# 764 "FStar.SMTEncoding.Encode.fst"
let env' = (push_term_var env x ee1)
in (
# 765 "FStar.SMTEncoding.Encode.fst"
let _86_1169 = (encode_body e2 env')
in (match (_86_1169) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (
# 769 "FStar.SMTEncoding.Encode.fst"
let _86_1177 = (encode_term e env)
in (match (_86_1177) with
| (scr, decls) -> begin
(
# 770 "FStar.SMTEncoding.Encode.fst"
let _86_1214 = (FStar_List.fold_right (fun b _86_1181 -> (match (_86_1181) with
| (else_case, decls) -> begin
(
# 771 "FStar.SMTEncoding.Encode.fst"
let _86_1185 = (FStar_Syntax_Subst.open_branch b)
in (match (_86_1185) with
| (p, w, br) -> begin
(
# 772 "FStar.SMTEncoding.Encode.fst"
let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _86_1189 _86_1192 -> (match (((_86_1189), (_86_1192))) with
| ((env0, pattern), (else_case, decls)) -> begin
(
# 774 "FStar.SMTEncoding.Encode.fst"
let guard = (pattern.guard scr)
in (
# 775 "FStar.SMTEncoding.Encode.fst"
let projections = (pattern.projections scr)
in (
# 776 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _86_1198 -> (match (_86_1198) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (
# 777 "FStar.SMTEncoding.Encode.fst"
let _86_1208 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(
# 780 "FStar.SMTEncoding.Encode.fst"
let _86_1205 = (encode_term w env)
in (match (_86_1205) with
| (w, decls2) -> begin
(let _179_757 = (let _179_756 = (let _179_755 = (let _179_754 = (let _179_753 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in ((w), (_179_753)))
in (FStar_SMTEncoding_Term.mkEq _179_754))
in ((guard), (_179_755)))
in (FStar_SMTEncoding_Term.mkAnd _179_756))
in ((_179_757), (decls2)))
end))
end)
in (match (_86_1208) with
| (guard, decls2) -> begin
(
# 782 "FStar.SMTEncoding.Encode.fst"
let _86_1211 = (encode_br br env)
in (match (_86_1211) with
| (br, decls3) -> begin
(let _179_758 = (FStar_SMTEncoding_Term.mkITE ((guard), (br), (else_case)))
in ((_179_758), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (_86_1214) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _86_1220 -> begin
(let _179_761 = (encode_one_pat env pat)
in (_179_761)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (
# 796 "FStar.SMTEncoding.Encode.fst"
let _86_1223 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _179_764 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _179_764))
end else begin
()
end
in (
# 797 "FStar.SMTEncoding.Encode.fst"
let _86_1227 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_86_1227) with
| (vars, pat_term) -> begin
(
# 799 "FStar.SMTEncoding.Encode.fst"
let _86_1239 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _86_1230 v -> (match (_86_1230) with
| (env, vars) -> begin
(
# 800 "FStar.SMTEncoding.Encode.fst"
let _86_1236 = (gen_term_var env v)
in (match (_86_1236) with
| (xx, _86_1234, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (_86_1239) with
| (env, vars) -> begin
(
# 803 "FStar.SMTEncoding.Encode.fst"
let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_86_1244) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _179_772 = (let _179_771 = (encode_const c)
in ((scrutinee), (_179_771)))
in (FStar_SMTEncoding_Term.mkEq _179_772))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(
# 811 "FStar.SMTEncoding.Encode.fst"
let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (
# 812 "FStar.SMTEncoding.Encode.fst"
let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _86_1266 -> (match (_86_1266) with
| (arg, _86_1265) -> begin
(
# 813 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _179_775 = (FStar_SMTEncoding_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg _179_775)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (
# 817 "FStar.SMTEncoding.Encode.fst"
let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_86_1273) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_86_1283) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _179_783 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _86_1293 -> (match (_86_1293) with
| (arg, _86_1292) -> begin
(
# 829 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _179_782 = (FStar_SMTEncoding_Term.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg _179_782)))
end))))
in (FStar_All.pipe_right _179_783 FStar_List.flatten))
end))
in (
# 833 "FStar.SMTEncoding.Encode.fst"
let pat_term = (fun _86_1296 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (
# 835 "FStar.SMTEncoding.Encode.fst"
let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (
# 845 "FStar.SMTEncoding.Encode.fst"
let _86_1312 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _86_1302 _86_1306 -> (match (((_86_1302), (_86_1306))) with
| ((tms, decls), (t, _86_1305)) -> begin
(
# 846 "FStar.SMTEncoding.Encode.fst"
let _86_1309 = (encode_term t env)
in (match (_86_1309) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (_86_1312) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (
# 852 "FStar.SMTEncoding.Encode.fst"
let list_elements = (fun e -> (match ((FStar_Syntax_Util.list_elements e)) with
| Some (l) -> begin
l
end
| None -> begin
(
# 855 "FStar.SMTEncoding.Encode.fst"
let _86_1322 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (
# 857 "FStar.SMTEncoding.Encode.fst"
let one_pat = (fun p -> (
# 858 "FStar.SMTEncoding.Encode.fst"
let _86_1328 = (let _179_798 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _179_798 FStar_Syntax_Util.head_and_args))
in (match (_86_1328) with
| (head, args) -> begin
(match ((let _179_800 = (let _179_799 = (FStar_Syntax_Util.un_uinst head)
in _179_799.FStar_Syntax_Syntax.n)
in ((_179_800), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((_86_1336, _86_1338))::((e, _86_1333))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _86_1346))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| _86_1351 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (
# 864 "FStar.SMTEncoding.Encode.fst"
let lemma_pats = (fun p -> (
# 865 "FStar.SMTEncoding.Encode.fst"
let elts = (list_elements p)
in (
# 866 "FStar.SMTEncoding.Encode.fst"
let smt_pat_or = (fun t -> (
# 867 "FStar.SMTEncoding.Encode.fst"
let _86_1359 = (let _179_805 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _179_805 FStar_Syntax_Util.head_and_args))
in (match (_86_1359) with
| (head, args) -> begin
(match ((let _179_807 = (let _179_806 = (FStar_Syntax_Util.un_uinst head)
in _179_806.FStar_Syntax_Syntax.n)
in ((_179_807), (args)))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, _86_1364))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _86_1369 -> begin
None
end)
end)))
in (match (elts) with
| (t)::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _179_810 = (list_elements e)
in (FStar_All.pipe_right _179_810 (FStar_List.map (fun branch -> (let _179_809 = (list_elements branch)
in (FStar_All.pipe_right _179_809 (FStar_List.map one_pat)))))))
end
| _86_1376 -> begin
(let _179_811 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_179_811)::[])
end)
end
| _86_1378 -> begin
(let _179_812 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_179_812)::[])
end))))
in (
# 881 "FStar.SMTEncoding.Encode.fst"
let _86_1412 = (match ((let _179_813 = (FStar_Syntax_Subst.compress t)
in _179_813.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 883 "FStar.SMTEncoding.Encode.fst"
let _86_1385 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_86_1385) with
| (binders, c) -> begin
(
# 884 "FStar.SMTEncoding.Encode.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| ((pre, _86_1397))::((post, _86_1393))::((pats, _86_1389))::[] -> begin
(
# 887 "FStar.SMTEncoding.Encode.fst"
let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _179_814 = (lemma_pats pats')
in ((binders), (pre), (post), (_179_814))))
end
| _86_1405 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _86_1407 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_86_1412) with
| (binders, pre, post, patterns) -> begin
(
# 895 "FStar.SMTEncoding.Encode.fst"
let _86_1419 = (encode_binders None binders env)
in (match (_86_1419) with
| (vars, guards, env, decls, _86_1418) -> begin
(
# 898 "FStar.SMTEncoding.Encode.fst"
let _86_1432 = (let _179_818 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (
# 899 "FStar.SMTEncoding.Encode.fst"
let _86_1429 = (let _179_817 = (FStar_All.pipe_right branch (FStar_List.map (fun _86_1424 -> (match (_86_1424) with
| (t, _86_1423) -> begin
(encode_term t (
# 899 "FStar.SMTEncoding.Encode.fst"
let _86_1425 = env
in {bindings = _86_1425.bindings; depth = _86_1425.depth; tcenv = _86_1425.tcenv; warn = _86_1425.warn; cache = _86_1425.cache; nolabels = _86_1425.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _86_1425.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _179_817 FStar_List.unzip))
in (match (_86_1429) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right _179_818 FStar_List.unzip))
in (match (_86_1432) with
| (pats, decls') -> begin
(
# 902 "FStar.SMTEncoding.Encode.fst"
let decls' = (FStar_List.flatten decls')
in (
# 904 "FStar.SMTEncoding.Encode.fst"
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _179_821 = (let _179_820 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _179_820 e))
in (_179_821)::p))))
end
| _86_1442 -> begin
(
# 912 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _179_827 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_179_827)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(let _179_829 = (let _179_828 = (FStar_SMTEncoding_Term.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_LexCons _179_828 tl))
in (aux _179_829 vars))
end
| _86_1454 -> begin
pats
end))
in (let _179_830 = (FStar_SMTEncoding_Term.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux _179_830 vars)))
end)
end)
in (
# 919 "FStar.SMTEncoding.Encode.fst"
let env = (
# 919 "FStar.SMTEncoding.Encode.fst"
let _86_1456 = env
in {bindings = _86_1456.bindings; depth = _86_1456.depth; tcenv = _86_1456.tcenv; warn = _86_1456.warn; cache = _86_1456.cache; nolabels = true; use_zfuel_name = _86_1456.use_zfuel_name; encode_non_total_function_typ = _86_1456.encode_non_total_function_typ})
in (
# 920 "FStar.SMTEncoding.Encode.fst"
let _86_1461 = (let _179_831 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _179_831 env))
in (match (_86_1461) with
| (pre, decls'') -> begin
(
# 921 "FStar.SMTEncoding.Encode.fst"
let _86_1464 = (let _179_832 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _179_832 env))
in (match (_86_1464) with
| (post, decls''') -> begin
(
# 922 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (let _179_837 = (let _179_836 = (let _179_835 = (let _179_834 = (let _179_833 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in ((_179_833), (post)))
in (FStar_SMTEncoding_Term.mkImp _179_834))
in ((pats), (vars), (_179_835)))
in (FStar_SMTEncoding_Term.mkForall _179_836))
in ((_179_837), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (
# 926 "FStar.SMTEncoding.Encode.fst"
let debug = (fun phi -> if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _179_843 = (FStar_Syntax_Print.tag_of_term phi)
in (let _179_842 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" _179_843 _179_842)))
end else begin
()
end)
in (
# 931 "FStar.SMTEncoding.Encode.fst"
let enc = (fun f l -> (
# 932 "FStar.SMTEncoding.Encode.fst"
let _86_1480 = (FStar_Util.fold_map (fun decls x -> (
# 932 "FStar.SMTEncoding.Encode.fst"
let _86_1477 = (encode_term (Prims.fst x) env)
in (match (_86_1477) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (_86_1480) with
| (decls, args) -> begin
(let _179_859 = (f args)
in ((_179_859), (decls)))
end)))
in (
# 935 "FStar.SMTEncoding.Encode.fst"
let const_op = (fun f _86_1483 -> ((f), ([])))
in (
# 936 "FStar.SMTEncoding.Encode.fst"
let un_op = (fun f l -> (let _179_873 = (FStar_List.hd l)
in (FStar_All.pipe_left f _179_873)))
in (
# 937 "FStar.SMTEncoding.Encode.fst"
let bin_op = (fun f _86_10 -> (match (_86_10) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| _86_1494 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 941 "FStar.SMTEncoding.Encode.fst"
let enc_prop_c = (fun f l -> (
# 942 "FStar.SMTEncoding.Encode.fst"
let _86_1509 = (FStar_Util.fold_map (fun decls _86_1503 -> (match (_86_1503) with
| (t, _86_1502) -> begin
(
# 944 "FStar.SMTEncoding.Encode.fst"
let _86_1506 = (encode_formula t env)
in (match (_86_1506) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (_86_1509) with
| (decls, phis) -> begin
(let _179_898 = (f phis)
in ((_179_898), (decls)))
end)))
in (
# 949 "FStar.SMTEncoding.Encode.fst"
let eq_op = (fun _86_11 -> (match (_86_11) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (
# 954 "FStar.SMTEncoding.Encode.fst"
let mk_imp = (fun _86_12 -> (match (_86_12) with
| ((lhs, _86_1530))::((rhs, _86_1526))::[] -> begin
(
# 956 "FStar.SMTEncoding.Encode.fst"
let _86_1535 = (encode_formula rhs env)
in (match (_86_1535) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _86_1538) -> begin
((l1), (decls1))
end
| _86_1542 -> begin
(
# 960 "FStar.SMTEncoding.Encode.fst"
let _86_1545 = (encode_formula lhs env)
in (match (_86_1545) with
| (l2, decls2) -> begin
(let _179_903 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)))
in ((_179_903), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| _86_1547 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 965 "FStar.SMTEncoding.Encode.fst"
let mk_ite = (fun _86_13 -> (match (_86_13) with
| ((guard, _86_1560))::((_then, _86_1556))::((_else, _86_1552))::[] -> begin
(
# 967 "FStar.SMTEncoding.Encode.fst"
let _86_1565 = (encode_formula guard env)
in (match (_86_1565) with
| (g, decls1) -> begin
(
# 968 "FStar.SMTEncoding.Encode.fst"
let _86_1568 = (encode_formula _then env)
in (match (_86_1568) with
| (t, decls2) -> begin
(
# 969 "FStar.SMTEncoding.Encode.fst"
let _86_1571 = (encode_formula _else env)
in (match (_86_1571) with
| (e, decls3) -> begin
(
# 970 "FStar.SMTEncoding.Encode.fst"
let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)))
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| _86_1574 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 975 "FStar.SMTEncoding.Encode.fst"
let unboxInt_l = (fun f l -> (let _179_915 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _179_915)))
in (
# 976 "FStar.SMTEncoding.Encode.fst"
let connectives = (let _179_971 = (let _179_924 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in ((FStar_Syntax_Const.and_lid), (_179_924)))
in (let _179_970 = (let _179_969 = (let _179_930 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in ((FStar_Syntax_Const.or_lid), (_179_930)))
in (let _179_968 = (let _179_967 = (let _179_966 = (let _179_939 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in ((FStar_Syntax_Const.iff_lid), (_179_939)))
in (let _179_965 = (let _179_964 = (let _179_963 = (let _179_948 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in ((FStar_Syntax_Const.not_lid), (_179_948)))
in (_179_963)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::_179_964)
in (_179_966)::_179_965))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::_179_967)
in (_179_969)::_179_968))
in (_179_971)::_179_970))
in (
# 989 "FStar.SMTEncoding.Encode.fst"
let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(
# 991 "FStar.SMTEncoding.Encode.fst"
let _86_1592 = (encode_formula phi' env)
in (match (_86_1592) with
| (phi, decls) -> begin
(let _179_974 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))))
in ((_179_974), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (_86_1594) -> begin
(let _179_975 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula _179_975 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(
# 998 "FStar.SMTEncoding.Encode.fst"
let _86_1602 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_86_1602) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _86_1609; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _86_1606; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(
# 1002 "FStar.SMTEncoding.Encode.fst"
let _86_1620 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_86_1620) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 1006 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_86_1637)::((x, _86_1634))::((t, _86_1630))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(
# 1009 "FStar.SMTEncoding.Encode.fst"
let _86_1642 = (encode_term x env)
in (match (_86_1642) with
| (x, decls) -> begin
(
# 1010 "FStar.SMTEncoding.Encode.fst"
let _86_1645 = (encode_term t env)
in (match (_86_1645) with
| (t, decls') -> begin
(let _179_976 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((_179_976), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, _86_1658))::((msg, _86_1654))::((phi, _86_1650))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _179_980 = (let _179_977 = (FStar_Syntax_Subst.compress r)
in _179_977.FStar_Syntax_Syntax.n)
in (let _179_979 = (let _179_978 = (FStar_Syntax_Subst.compress msg)
in _179_978.FStar_Syntax_Syntax.n)
in ((_179_980), (_179_979))))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _86_1667))) -> begin
(
# 1016 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false))))))) None r)
in (fallback phi))
end
| _86_1674 -> begin
(fallback phi)
end)
end
| _86_1676 when (head_redex env head) -> begin
(let _179_981 = (whnf env phi)
in (encode_formula _179_981 env))
end
| _86_1678 -> begin
(
# 1026 "FStar.SMTEncoding.Encode.fst"
let _86_1681 = (encode_term phi env)
in (match (_86_1681) with
| (tt, decls) -> begin
(let _179_982 = (FStar_SMTEncoding_Term.mk_Valid tt)
in ((_179_982), (decls)))
end))
end))
end
| _86_1683 -> begin
(
# 1031 "FStar.SMTEncoding.Encode.fst"
let _86_1686 = (encode_term phi env)
in (match (_86_1686) with
| (tt, decls) -> begin
(let _179_983 = (FStar_SMTEncoding_Term.mk_Valid tt)
in ((_179_983), (decls)))
end))
end))
in (
# 1034 "FStar.SMTEncoding.Encode.fst"
let encode_q_body = (fun env bs ps body -> (
# 1035 "FStar.SMTEncoding.Encode.fst"
let _86_1698 = (encode_binders None bs env)
in (match (_86_1698) with
| (vars, guards, env, decls, _86_1697) -> begin
(
# 1036 "FStar.SMTEncoding.Encode.fst"
let _86_1711 = (let _179_995 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (
# 1037 "FStar.SMTEncoding.Encode.fst"
let _86_1708 = (let _179_994 = (FStar_All.pipe_right p (FStar_List.map (fun _86_1703 -> (match (_86_1703) with
| (t, _86_1702) -> begin
(encode_term t (
# 1037 "FStar.SMTEncoding.Encode.fst"
let _86_1704 = env
in {bindings = _86_1704.bindings; depth = _86_1704.depth; tcenv = _86_1704.tcenv; warn = _86_1704.warn; cache = _86_1704.cache; nolabels = _86_1704.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _86_1704.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _179_994 FStar_List.unzip))
in (match (_86_1708) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right _179_995 FStar_List.unzip))
in (match (_86_1711) with
| (pats, decls') -> begin
(
# 1039 "FStar.SMTEncoding.Encode.fst"
let _86_1714 = (encode_formula body env)
in (match (_86_1714) with
| (body, decls'') -> begin
(
# 1040 "FStar.SMTEncoding.Encode.fst"
let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.hash = _86_1718; FStar_SMTEncoding_Term.freevars = _86_1716})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| _86_1729 -> begin
guards
end)
in (let _179_996 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((vars), (pats), (_179_996), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in (
# 1045 "FStar.SMTEncoding.Encode.fst"
let _86_1731 = (debug phi)
in (
# 1047 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _86_1743 -> (match (_86_1743) with
| (l, _86_1742) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_86_1746, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(
# 1057 "FStar.SMTEncoding.Encode.fst"
let _86_1756 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _179_1013 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _179_1013))
end else begin
()
end
in (
# 1060 "FStar.SMTEncoding.Encode.fst"
let _86_1763 = (encode_q_body env vars pats body)
in (match (_86_1763) with
| (vars, pats, guard, body, decls) -> begin
(
# 1061 "FStar.SMTEncoding.Encode.fst"
let tm = (let _179_1015 = (let _179_1014 = (FStar_SMTEncoding_Term.mkImp ((guard), (body)))
in ((pats), (vars), (_179_1014)))
in (FStar_SMTEncoding_Term.mkForall _179_1015))
in (
# 1063 "FStar.SMTEncoding.Encode.fst"
let _86_1765 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _179_1016 = (FStar_SMTEncoding_Term.termToSmt tm)
in (FStar_Util.print1 ">>>> Encoded QALL to %s\n" _179_1016))
end else begin
()
end
in ((tm), (decls))))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(
# 1070 "FStar.SMTEncoding.Encode.fst"
let _86_1778 = (encode_q_body env vars pats body)
in (match (_86_1778) with
| (vars, pats, guard, body, decls) -> begin
(let _179_1019 = (let _179_1018 = (let _179_1017 = (FStar_SMTEncoding_Term.mkAnd ((guard), (body)))
in ((pats), (vars), (_179_1017)))
in (FStar_SMTEncoding_Term.mkExists _179_1018))
in ((_179_1019), (decls)))
end))
end)))))))))))))))))

# 1071 "FStar.SMTEncoding.Encode.fst"
type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}

# 1079 "FStar.SMTEncoding.Encode.fst"
let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))

# 1082 "FStar.SMTEncoding.Encode.fst"
let prims : prims_t = (
# 1086 "FStar.SMTEncoding.Encode.fst"
let _86_1784 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_86_1784) with
| (asym, a) -> begin
(
# 1087 "FStar.SMTEncoding.Encode.fst"
let _86_1787 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_86_1787) with
| (xsym, x) -> begin
(
# 1088 "FStar.SMTEncoding.Encode.fst"
let _86_1790 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_86_1790) with
| (ysym, y) -> begin
(
# 1089 "FStar.SMTEncoding.Encode.fst"
let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun (((x), (vars), (FStar_SMTEncoding_Term.Term_sort), (body), (None))))::[])
in (
# 1090 "FStar.SMTEncoding.Encode.fst"
let quant = (fun vars body x -> (
# 1091 "FStar.SMTEncoding.Encode.fst"
let xname_decl = (let _179_1062 = (let _179_1061 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (_179_1061), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_179_1062))
in (
# 1092 "FStar.SMTEncoding.Encode.fst"
let xtok = (Prims.strcat x "@tok")
in (
# 1093 "FStar.SMTEncoding.Encode.fst"
let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (
# 1094 "FStar.SMTEncoding.Encode.fst"
let xapp = (let _179_1064 = (let _179_1063 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((x), (_179_1063)))
in (FStar_SMTEncoding_Term.mkApp _179_1064))
in (
# 1095 "FStar.SMTEncoding.Encode.fst"
let xtok = (FStar_SMTEncoding_Term.mkApp ((xtok), ([])))
in (
# 1096 "FStar.SMTEncoding.Encode.fst"
let xtok_app = (mk_Apply xtok vars)
in (let _179_1078 = (let _179_1077 = (let _179_1076 = (let _179_1075 = (let _179_1068 = (let _179_1067 = (let _179_1066 = (let _179_1065 = (FStar_SMTEncoding_Term.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (_179_1065)))
in (FStar_SMTEncoding_Term.mkForall _179_1066))
in ((_179_1067), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (_179_1068))
in (let _179_1074 = (let _179_1073 = (let _179_1072 = (let _179_1071 = (let _179_1070 = (let _179_1069 = (FStar_SMTEncoding_Term.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (_179_1069)))
in (FStar_SMTEncoding_Term.mkForall _179_1070))
in ((_179_1071), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x)))))
in FStar_SMTEncoding_Term.Assume (_179_1072))
in (_179_1073)::[])
in (_179_1075)::_179_1074))
in (xtok_decl)::_179_1076)
in (xname_decl)::_179_1077)
in ((xtok), (_179_1078))))))))))
in (
# 1105 "FStar.SMTEncoding.Encode.fst"
let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (
# 1106 "FStar.SMTEncoding.Encode.fst"
let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (
# 1107 "FStar.SMTEncoding.Encode.fst"
let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (
# 1108 "FStar.SMTEncoding.Encode.fst"
let prims = (let _179_1238 = (let _179_1087 = (let _179_1086 = (let _179_1085 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _179_1085))
in (quant axy _179_1086))
in ((FStar_Syntax_Const.op_Eq), (_179_1087)))
in (let _179_1237 = (let _179_1236 = (let _179_1094 = (let _179_1093 = (let _179_1092 = (let _179_1091 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in (FStar_SMTEncoding_Term.mkNot _179_1091))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _179_1092))
in (quant axy _179_1093))
in ((FStar_Syntax_Const.op_notEq), (_179_1094)))
in (let _179_1235 = (let _179_1234 = (let _179_1103 = (let _179_1102 = (let _179_1101 = (let _179_1100 = (let _179_1099 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _179_1098 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_179_1099), (_179_1098))))
in (FStar_SMTEncoding_Term.mkLT _179_1100))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _179_1101))
in (quant xy _179_1102))
in ((FStar_Syntax_Const.op_LT), (_179_1103)))
in (let _179_1233 = (let _179_1232 = (let _179_1112 = (let _179_1111 = (let _179_1110 = (let _179_1109 = (let _179_1108 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _179_1107 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_179_1108), (_179_1107))))
in (FStar_SMTEncoding_Term.mkLTE _179_1109))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _179_1110))
in (quant xy _179_1111))
in ((FStar_Syntax_Const.op_LTE), (_179_1112)))
in (let _179_1231 = (let _179_1230 = (let _179_1121 = (let _179_1120 = (let _179_1119 = (let _179_1118 = (let _179_1117 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _179_1116 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_179_1117), (_179_1116))))
in (FStar_SMTEncoding_Term.mkGT _179_1118))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _179_1119))
in (quant xy _179_1120))
in ((FStar_Syntax_Const.op_GT), (_179_1121)))
in (let _179_1229 = (let _179_1228 = (let _179_1130 = (let _179_1129 = (let _179_1128 = (let _179_1127 = (let _179_1126 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _179_1125 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_179_1126), (_179_1125))))
in (FStar_SMTEncoding_Term.mkGTE _179_1127))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _179_1128))
in (quant xy _179_1129))
in ((FStar_Syntax_Const.op_GTE), (_179_1130)))
in (let _179_1227 = (let _179_1226 = (let _179_1139 = (let _179_1138 = (let _179_1137 = (let _179_1136 = (let _179_1135 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _179_1134 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_179_1135), (_179_1134))))
in (FStar_SMTEncoding_Term.mkSub _179_1136))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _179_1137))
in (quant xy _179_1138))
in ((FStar_Syntax_Const.op_Subtraction), (_179_1139)))
in (let _179_1225 = (let _179_1224 = (let _179_1146 = (let _179_1145 = (let _179_1144 = (let _179_1143 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _179_1143))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _179_1144))
in (quant qx _179_1145))
in ((FStar_Syntax_Const.op_Minus), (_179_1146)))
in (let _179_1223 = (let _179_1222 = (let _179_1155 = (let _179_1154 = (let _179_1153 = (let _179_1152 = (let _179_1151 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _179_1150 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_179_1151), (_179_1150))))
in (FStar_SMTEncoding_Term.mkAdd _179_1152))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _179_1153))
in (quant xy _179_1154))
in ((FStar_Syntax_Const.op_Addition), (_179_1155)))
in (let _179_1221 = (let _179_1220 = (let _179_1164 = (let _179_1163 = (let _179_1162 = (let _179_1161 = (let _179_1160 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _179_1159 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_179_1160), (_179_1159))))
in (FStar_SMTEncoding_Term.mkMul _179_1161))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _179_1162))
in (quant xy _179_1163))
in ((FStar_Syntax_Const.op_Multiply), (_179_1164)))
in (let _179_1219 = (let _179_1218 = (let _179_1173 = (let _179_1172 = (let _179_1171 = (let _179_1170 = (let _179_1169 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _179_1168 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_179_1169), (_179_1168))))
in (FStar_SMTEncoding_Term.mkDiv _179_1170))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _179_1171))
in (quant xy _179_1172))
in ((FStar_Syntax_Const.op_Division), (_179_1173)))
in (let _179_1217 = (let _179_1216 = (let _179_1182 = (let _179_1181 = (let _179_1180 = (let _179_1179 = (let _179_1178 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _179_1177 = (FStar_SMTEncoding_Term.unboxInt y)
in ((_179_1178), (_179_1177))))
in (FStar_SMTEncoding_Term.mkMod _179_1179))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _179_1180))
in (quant xy _179_1181))
in ((FStar_Syntax_Const.op_Modulus), (_179_1182)))
in (let _179_1215 = (let _179_1214 = (let _179_1191 = (let _179_1190 = (let _179_1189 = (let _179_1188 = (let _179_1187 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _179_1186 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_179_1187), (_179_1186))))
in (FStar_SMTEncoding_Term.mkAnd _179_1188))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _179_1189))
in (quant xy _179_1190))
in ((FStar_Syntax_Const.op_And), (_179_1191)))
in (let _179_1213 = (let _179_1212 = (let _179_1200 = (let _179_1199 = (let _179_1198 = (let _179_1197 = (let _179_1196 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _179_1195 = (FStar_SMTEncoding_Term.unboxBool y)
in ((_179_1196), (_179_1195))))
in (FStar_SMTEncoding_Term.mkOr _179_1197))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _179_1198))
in (quant xy _179_1199))
in ((FStar_Syntax_Const.op_Or), (_179_1200)))
in (let _179_1211 = (let _179_1210 = (let _179_1207 = (let _179_1206 = (let _179_1205 = (let _179_1204 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _179_1204))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _179_1205))
in (quant qx _179_1206))
in ((FStar_Syntax_Const.op_Negation), (_179_1207)))
in (_179_1210)::[])
in (_179_1212)::_179_1211))
in (_179_1214)::_179_1213))
in (_179_1216)::_179_1215))
in (_179_1218)::_179_1217))
in (_179_1220)::_179_1219))
in (_179_1222)::_179_1221))
in (_179_1224)::_179_1223))
in (_179_1226)::_179_1225))
in (_179_1228)::_179_1227))
in (_179_1230)::_179_1229))
in (_179_1232)::_179_1231))
in (_179_1234)::_179_1233))
in (_179_1236)::_179_1235))
in (_179_1238)::_179_1237))
in (
# 1125 "FStar.SMTEncoding.Encode.fst"
let mk = (fun l v -> (let _179_1285 = (let _179_1284 = (FStar_All.pipe_right prims (FStar_List.find (fun _86_1814 -> (match (_86_1814) with
| (l', _86_1813) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _179_1284 (FStar_Option.map (fun _86_1818 -> (match (_86_1818) with
| (_86_1816, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right _179_1285 FStar_Option.get)))
in (
# 1127 "FStar.SMTEncoding.Encode.fst"
let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _86_1824 -> (match (_86_1824) with
| (l', _86_1823) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

# 1130 "FStar.SMTEncoding.Encode.fst"
let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (
# 1133 "FStar.SMTEncoding.Encode.fst"
let _86_1830 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_86_1830) with
| (xxsym, xx) -> begin
(
# 1134 "FStar.SMTEncoding.Encode.fst"
let _86_1833 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_86_1833) with
| (ffsym, ff) -> begin
(
# 1135 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _179_1315 = (let _179_1314 = (let _179_1309 = (let _179_1308 = (let _179_1307 = (let _179_1306 = (let _179_1305 = (let _179_1304 = (FStar_SMTEncoding_Term.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (_179_1304)))
in (FStar_SMTEncoding_Term.mkEq _179_1305))
in ((xx_has_type), (_179_1306)))
in (FStar_SMTEncoding_Term.mkImp _179_1307))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (_179_1308)))
in (FStar_SMTEncoding_Term.mkForall _179_1309))
in (let _179_1313 = (let _179_1312 = (let _179_1311 = (let _179_1310 = (FStar_Util.digest_of_string tapp.FStar_SMTEncoding_Term.hash)
in (Prims.strcat "pretyping_" _179_1310))
in (varops.mk_unique _179_1311))
in Some (_179_1312))
in ((_179_1314), (Some ("pretyping")), (_179_1313))))
in FStar_SMTEncoding_Term.Assume (_179_1315)))
end))
end)))

# 1137 "FStar.SMTEncoding.Encode.fst"
let primitive_type_axioms : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (
# 1140 "FStar.SMTEncoding.Encode.fst"
let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1141 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1143 "FStar.SMTEncoding.Encode.fst"
let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1144 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1146 "FStar.SMTEncoding.Encode.fst"
let mk_unit = (fun env nm tt -> (
# 1147 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _179_1336 = (let _179_1327 = (let _179_1326 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((_179_1326), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (_179_1327))
in (let _179_1335 = (let _179_1334 = (let _179_1333 = (let _179_1332 = (let _179_1331 = (let _179_1330 = (let _179_1329 = (let _179_1328 = (FStar_SMTEncoding_Term.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (_179_1328)))
in (FStar_SMTEncoding_Term.mkImp _179_1329))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_179_1330)))
in (mkForall_fuel _179_1331))
in ((_179_1332), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (_179_1333))
in (_179_1334)::[])
in (_179_1336)::_179_1335))))
in (
# 1150 "FStar.SMTEncoding.Encode.fst"
let mk_bool = (fun env nm tt -> (
# 1151 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1152 "FStar.SMTEncoding.Encode.fst"
let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (
# 1153 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _179_1359 = (let _179_1350 = (let _179_1349 = (let _179_1348 = (let _179_1347 = (let _179_1344 = (let _179_1343 = (FStar_SMTEncoding_Term.boxBool b)
in (_179_1343)::[])
in (_179_1344)::[])
in (let _179_1346 = (let _179_1345 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _179_1345 tt))
in ((_179_1347), ((bb)::[]), (_179_1346))))
in (FStar_SMTEncoding_Term.mkForall _179_1348))
in ((_179_1349), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (_179_1350))
in (let _179_1358 = (let _179_1357 = (let _179_1356 = (let _179_1355 = (let _179_1354 = (let _179_1353 = (let _179_1352 = (let _179_1351 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (_179_1351)))
in (FStar_SMTEncoding_Term.mkImp _179_1352))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_179_1353)))
in (mkForall_fuel _179_1354))
in ((_179_1355), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (_179_1356))
in (_179_1357)::[])
in (_179_1359)::_179_1358))))))
in (
# 1156 "FStar.SMTEncoding.Encode.fst"
let mk_int = (fun env nm tt -> (
# 1157 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1158 "FStar.SMTEncoding.Encode.fst"
let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (
# 1159 "FStar.SMTEncoding.Encode.fst"
let aa = (("a"), (FStar_SMTEncoding_Term.Int_sort))
in (
# 1160 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1161 "FStar.SMTEncoding.Encode.fst"
let bb = (("b"), (FStar_SMTEncoding_Term.Int_sort))
in (
# 1162 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1163 "FStar.SMTEncoding.Encode.fst"
let precedes = (let _179_1373 = (let _179_1372 = (let _179_1371 = (let _179_1370 = (let _179_1369 = (let _179_1368 = (FStar_SMTEncoding_Term.boxInt a)
in (let _179_1367 = (let _179_1366 = (FStar_SMTEncoding_Term.boxInt b)
in (_179_1366)::[])
in (_179_1368)::_179_1367))
in (tt)::_179_1369)
in (tt)::_179_1370)
in (("Prims.Precedes"), (_179_1371)))
in (FStar_SMTEncoding_Term.mkApp _179_1372))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _179_1373))
in (
# 1164 "FStar.SMTEncoding.Encode.fst"
let precedes_y_x = (let _179_1374 = (FStar_SMTEncoding_Term.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _179_1374))
in (let _179_1416 = (let _179_1382 = (let _179_1381 = (let _179_1380 = (let _179_1379 = (let _179_1376 = (let _179_1375 = (FStar_SMTEncoding_Term.boxInt b)
in (_179_1375)::[])
in (_179_1376)::[])
in (let _179_1378 = (let _179_1377 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _179_1377 tt))
in ((_179_1379), ((bb)::[]), (_179_1378))))
in (FStar_SMTEncoding_Term.mkForall _179_1380))
in ((_179_1381), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (_179_1382))
in (let _179_1415 = (let _179_1414 = (let _179_1388 = (let _179_1387 = (let _179_1386 = (let _179_1385 = (let _179_1384 = (let _179_1383 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (_179_1383)))
in (FStar_SMTEncoding_Term.mkImp _179_1384))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_179_1385)))
in (mkForall_fuel _179_1386))
in ((_179_1387), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (_179_1388))
in (let _179_1413 = (let _179_1412 = (let _179_1411 = (let _179_1410 = (let _179_1409 = (let _179_1408 = (let _179_1407 = (let _179_1406 = (let _179_1405 = (let _179_1404 = (let _179_1403 = (let _179_1402 = (let _179_1391 = (let _179_1390 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _179_1389 = (FStar_SMTEncoding_Term.mkInteger' 0)
in ((_179_1390), (_179_1389))))
in (FStar_SMTEncoding_Term.mkGT _179_1391))
in (let _179_1401 = (let _179_1400 = (let _179_1394 = (let _179_1393 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _179_1392 = (FStar_SMTEncoding_Term.mkInteger' 0)
in ((_179_1393), (_179_1392))))
in (FStar_SMTEncoding_Term.mkGTE _179_1394))
in (let _179_1399 = (let _179_1398 = (let _179_1397 = (let _179_1396 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _179_1395 = (FStar_SMTEncoding_Term.unboxInt x)
in ((_179_1396), (_179_1395))))
in (FStar_SMTEncoding_Term.mkLT _179_1397))
in (_179_1398)::[])
in (_179_1400)::_179_1399))
in (_179_1402)::_179_1401))
in (typing_pred_y)::_179_1403)
in (typing_pred)::_179_1404)
in (FStar_SMTEncoding_Term.mk_and_l _179_1405))
in ((_179_1406), (precedes_y_x)))
in (FStar_SMTEncoding_Term.mkImp _179_1407))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (_179_1408)))
in (mkForall_fuel _179_1409))
in ((_179_1410), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (_179_1411))
in (_179_1412)::[])
in (_179_1414)::_179_1413))
in (_179_1416)::_179_1415)))))))))))
in (
# 1176 "FStar.SMTEncoding.Encode.fst"
let mk_str = (fun env nm tt -> (
# 1177 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1178 "FStar.SMTEncoding.Encode.fst"
let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (
# 1179 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _179_1439 = (let _179_1430 = (let _179_1429 = (let _179_1428 = (let _179_1427 = (let _179_1424 = (let _179_1423 = (FStar_SMTEncoding_Term.boxString b)
in (_179_1423)::[])
in (_179_1424)::[])
in (let _179_1426 = (let _179_1425 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _179_1425 tt))
in ((_179_1427), ((bb)::[]), (_179_1426))))
in (FStar_SMTEncoding_Term.mkForall _179_1428))
in ((_179_1429), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (_179_1430))
in (let _179_1438 = (let _179_1437 = (let _179_1436 = (let _179_1435 = (let _179_1434 = (let _179_1433 = (let _179_1432 = (let _179_1431 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (_179_1431)))
in (FStar_SMTEncoding_Term.mkImp _179_1432))
in ((((typing_pred)::[])::[]), ((xx)::[]), (_179_1433)))
in (mkForall_fuel _179_1434))
in ((_179_1435), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (_179_1436))
in (_179_1437)::[])
in (_179_1439)::_179_1438))))))
in (
# 1182 "FStar.SMTEncoding.Encode.fst"
let mk_ref = (fun env reft_name _86_1872 -> (
# 1183 "FStar.SMTEncoding.Encode.fst"
let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (
# 1184 "FStar.SMTEncoding.Encode.fst"
let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1185 "FStar.SMTEncoding.Encode.fst"
let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1186 "FStar.SMTEncoding.Encode.fst"
let refa = (let _179_1448 = (let _179_1447 = (let _179_1446 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_179_1446)::[])
in ((reft_name), (_179_1447)))
in (FStar_SMTEncoding_Term.mkApp _179_1448))
in (
# 1187 "FStar.SMTEncoding.Encode.fst"
let refb = (let _179_1451 = (let _179_1450 = (let _179_1449 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_179_1449)::[])
in ((reft_name), (_179_1450)))
in (FStar_SMTEncoding_Term.mkApp _179_1451))
in (
# 1188 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (
# 1189 "FStar.SMTEncoding.Encode.fst"
let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _179_1470 = (let _179_1457 = (let _179_1456 = (let _179_1455 = (let _179_1454 = (let _179_1453 = (let _179_1452 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (_179_1452)))
in (FStar_SMTEncoding_Term.mkImp _179_1453))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (_179_1454)))
in (mkForall_fuel _179_1455))
in ((_179_1456), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (_179_1457))
in (let _179_1469 = (let _179_1468 = (let _179_1467 = (let _179_1466 = (let _179_1465 = (let _179_1464 = (let _179_1463 = (let _179_1462 = (FStar_SMTEncoding_Term.mkAnd ((typing_pred), (typing_pred_b)))
in (let _179_1461 = (let _179_1460 = (let _179_1459 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _179_1458 = (FStar_SMTEncoding_Term.mkFreeV bb)
in ((_179_1459), (_179_1458))))
in (FStar_SMTEncoding_Term.mkEq _179_1460))
in ((_179_1462), (_179_1461))))
in (FStar_SMTEncoding_Term.mkImp _179_1463))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (_179_1464)))
in (mkForall_fuel' 2 _179_1465))
in ((_179_1466), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (_179_1467))
in (_179_1468)::[])
in (_179_1470)::_179_1469))))))))))
in (
# 1192 "FStar.SMTEncoding.Encode.fst"
let mk_false_interp = (fun env nm false_tm -> (
# 1193 "FStar.SMTEncoding.Encode.fst"
let valid = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((false_tm)::[])))
in (let _179_1479 = (let _179_1478 = (let _179_1477 = (FStar_SMTEncoding_Term.mkIff ((FStar_SMTEncoding_Term.mkFalse), (valid)))
in ((_179_1477), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (_179_1478))
in (_179_1479)::[])))
in (
# 1195 "FStar.SMTEncoding.Encode.fst"
let mk_and_interp = (fun env conj _86_1889 -> (
# 1196 "FStar.SMTEncoding.Encode.fst"
let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1197 "FStar.SMTEncoding.Encode.fst"
let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1198 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1199 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1200 "FStar.SMTEncoding.Encode.fst"
let valid = (let _179_1488 = (let _179_1487 = (let _179_1486 = (FStar_SMTEncoding_Term.mkApp ((conj), ((a)::(b)::[])))
in (_179_1486)::[])
in (("Valid"), (_179_1487)))
in (FStar_SMTEncoding_Term.mkApp _179_1488))
in (
# 1201 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (
# 1202 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _179_1495 = (let _179_1494 = (let _179_1493 = (let _179_1492 = (let _179_1491 = (let _179_1490 = (let _179_1489 = (FStar_SMTEncoding_Term.mkAnd ((valid_a), (valid_b)))
in ((_179_1489), (valid)))
in (FStar_SMTEncoding_Term.mkIff _179_1490))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_179_1491)))
in (FStar_SMTEncoding_Term.mkForall _179_1492))
in ((_179_1493), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (_179_1494))
in (_179_1495)::[])))))))))
in (
# 1204 "FStar.SMTEncoding.Encode.fst"
let mk_or_interp = (fun env disj _86_1901 -> (
# 1205 "FStar.SMTEncoding.Encode.fst"
let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1206 "FStar.SMTEncoding.Encode.fst"
let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1207 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1208 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1209 "FStar.SMTEncoding.Encode.fst"
let valid = (let _179_1504 = (let _179_1503 = (let _179_1502 = (FStar_SMTEncoding_Term.mkApp ((disj), ((a)::(b)::[])))
in (_179_1502)::[])
in (("Valid"), (_179_1503)))
in (FStar_SMTEncoding_Term.mkApp _179_1504))
in (
# 1210 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (
# 1211 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _179_1511 = (let _179_1510 = (let _179_1509 = (let _179_1508 = (let _179_1507 = (let _179_1506 = (let _179_1505 = (FStar_SMTEncoding_Term.mkOr ((valid_a), (valid_b)))
in ((_179_1505), (valid)))
in (FStar_SMTEncoding_Term.mkIff _179_1506))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_179_1507)))
in (FStar_SMTEncoding_Term.mkForall _179_1508))
in ((_179_1509), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (_179_1510))
in (_179_1511)::[])))))))))
in (
# 1213 "FStar.SMTEncoding.Encode.fst"
let mk_eq2_interp = (fun env eq2 tt -> (
# 1214 "FStar.SMTEncoding.Encode.fst"
let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1215 "FStar.SMTEncoding.Encode.fst"
let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1216 "FStar.SMTEncoding.Encode.fst"
let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1217 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1218 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1219 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1220 "FStar.SMTEncoding.Encode.fst"
let valid = (let _179_1520 = (let _179_1519 = (let _179_1518 = (FStar_SMTEncoding_Term.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (_179_1518)::[])
in (("Valid"), (_179_1519)))
in (FStar_SMTEncoding_Term.mkApp _179_1520))
in (let _179_1527 = (let _179_1526 = (let _179_1525 = (let _179_1524 = (let _179_1523 = (let _179_1522 = (let _179_1521 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in ((_179_1521), (valid)))
in (FStar_SMTEncoding_Term.mkIff _179_1522))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (_179_1523)))
in (FStar_SMTEncoding_Term.mkForall _179_1524))
in ((_179_1525), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (_179_1526))
in (_179_1527)::[])))))))))
in (
# 1222 "FStar.SMTEncoding.Encode.fst"
let mk_eq3_interp = (fun env eq3 tt -> (
# 1223 "FStar.SMTEncoding.Encode.fst"
let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1224 "FStar.SMTEncoding.Encode.fst"
let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1225 "FStar.SMTEncoding.Encode.fst"
let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1226 "FStar.SMTEncoding.Encode.fst"
let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1227 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1228 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1229 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1230 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1231 "FStar.SMTEncoding.Encode.fst"
let valid = (let _179_1536 = (let _179_1535 = (let _179_1534 = (FStar_SMTEncoding_Term.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (_179_1534)::[])
in (("Valid"), (_179_1535)))
in (FStar_SMTEncoding_Term.mkApp _179_1536))
in (let _179_1543 = (let _179_1542 = (let _179_1541 = (let _179_1540 = (let _179_1539 = (let _179_1538 = (let _179_1537 = (FStar_SMTEncoding_Term.mkEq ((x), (y)))
in ((_179_1537), (valid)))
in (FStar_SMTEncoding_Term.mkIff _179_1538))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (_179_1539)))
in (FStar_SMTEncoding_Term.mkForall _179_1540))
in ((_179_1541), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (_179_1542))
in (_179_1543)::[])))))))))))
in (
# 1233 "FStar.SMTEncoding.Encode.fst"
let mk_imp_interp = (fun env imp tt -> (
# 1234 "FStar.SMTEncoding.Encode.fst"
let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1235 "FStar.SMTEncoding.Encode.fst"
let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1236 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1237 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1238 "FStar.SMTEncoding.Encode.fst"
let valid = (let _179_1552 = (let _179_1551 = (let _179_1550 = (FStar_SMTEncoding_Term.mkApp ((imp), ((a)::(b)::[])))
in (_179_1550)::[])
in (("Valid"), (_179_1551)))
in (FStar_SMTEncoding_Term.mkApp _179_1552))
in (
# 1239 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (
# 1240 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _179_1559 = (let _179_1558 = (let _179_1557 = (let _179_1556 = (let _179_1555 = (let _179_1554 = (let _179_1553 = (FStar_SMTEncoding_Term.mkImp ((valid_a), (valid_b)))
in ((_179_1553), (valid)))
in (FStar_SMTEncoding_Term.mkIff _179_1554))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_179_1555)))
in (FStar_SMTEncoding_Term.mkForall _179_1556))
in ((_179_1557), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (_179_1558))
in (_179_1559)::[])))))))))
in (
# 1242 "FStar.SMTEncoding.Encode.fst"
let mk_iff_interp = (fun env iff tt -> (
# 1243 "FStar.SMTEncoding.Encode.fst"
let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1244 "FStar.SMTEncoding.Encode.fst"
let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1245 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1246 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1247 "FStar.SMTEncoding.Encode.fst"
let valid = (let _179_1568 = (let _179_1567 = (let _179_1566 = (FStar_SMTEncoding_Term.mkApp ((iff), ((a)::(b)::[])))
in (_179_1566)::[])
in (("Valid"), (_179_1567)))
in (FStar_SMTEncoding_Term.mkApp _179_1568))
in (
# 1248 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((a)::[])))
in (
# 1249 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp (("Valid"), ((b)::[])))
in (let _179_1575 = (let _179_1574 = (let _179_1573 = (let _179_1572 = (let _179_1571 = (let _179_1570 = (let _179_1569 = (FStar_SMTEncoding_Term.mkIff ((valid_a), (valid_b)))
in ((_179_1569), (valid)))
in (FStar_SMTEncoding_Term.mkIff _179_1570))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_179_1571)))
in (FStar_SMTEncoding_Term.mkForall _179_1572))
in ((_179_1573), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (_179_1574))
in (_179_1575)::[])))))))))
in (
# 1251 "FStar.SMTEncoding.Encode.fst"
let mk_forall_interp = (fun env for_all tt -> (
# 1252 "FStar.SMTEncoding.Encode.fst"
let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1253 "FStar.SMTEncoding.Encode.fst"
let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1254 "FStar.SMTEncoding.Encode.fst"
let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1255 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1256 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1257 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1258 "FStar.SMTEncoding.Encode.fst"
let valid = (let _179_1584 = (let _179_1583 = (let _179_1582 = (FStar_SMTEncoding_Term.mkApp ((for_all), ((a)::(b)::[])))
in (_179_1582)::[])
in (("Valid"), (_179_1583)))
in (FStar_SMTEncoding_Term.mkApp _179_1584))
in (
# 1259 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _179_1587 = (let _179_1586 = (let _179_1585 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_179_1585)::[])
in (("Valid"), (_179_1586)))
in (FStar_SMTEncoding_Term.mkApp _179_1587))
in (let _179_1601 = (let _179_1600 = (let _179_1599 = (let _179_1598 = (let _179_1597 = (let _179_1596 = (let _179_1595 = (let _179_1594 = (let _179_1593 = (let _179_1589 = (let _179_1588 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_179_1588)::[])
in (_179_1589)::[])
in (let _179_1592 = (let _179_1591 = (let _179_1590 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_179_1590), (valid_b_x)))
in (FStar_SMTEncoding_Term.mkImp _179_1591))
in ((_179_1593), ((xx)::[]), (_179_1592))))
in (FStar_SMTEncoding_Term.mkForall _179_1594))
in ((_179_1595), (valid)))
in (FStar_SMTEncoding_Term.mkIff _179_1596))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_179_1597)))
in (FStar_SMTEncoding_Term.mkForall _179_1598))
in ((_179_1599), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (_179_1600))
in (_179_1601)::[]))))))))))
in (
# 1263 "FStar.SMTEncoding.Encode.fst"
let mk_exists_interp = (fun env for_some tt -> (
# 1264 "FStar.SMTEncoding.Encode.fst"
let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1265 "FStar.SMTEncoding.Encode.fst"
let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1266 "FStar.SMTEncoding.Encode.fst"
let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1267 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1268 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1269 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1270 "FStar.SMTEncoding.Encode.fst"
let valid = (let _179_1610 = (let _179_1609 = (let _179_1608 = (FStar_SMTEncoding_Term.mkApp ((for_some), ((a)::(b)::[])))
in (_179_1608)::[])
in (("Valid"), (_179_1609)))
in (FStar_SMTEncoding_Term.mkApp _179_1610))
in (
# 1271 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _179_1613 = (let _179_1612 = (let _179_1611 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_179_1611)::[])
in (("Valid"), (_179_1612)))
in (FStar_SMTEncoding_Term.mkApp _179_1613))
in (let _179_1627 = (let _179_1626 = (let _179_1625 = (let _179_1624 = (let _179_1623 = (let _179_1622 = (let _179_1621 = (let _179_1620 = (let _179_1619 = (let _179_1615 = (let _179_1614 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_179_1614)::[])
in (_179_1615)::[])
in (let _179_1618 = (let _179_1617 = (let _179_1616 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((_179_1616), (valid_b_x)))
in (FStar_SMTEncoding_Term.mkImp _179_1617))
in ((_179_1619), ((xx)::[]), (_179_1618))))
in (FStar_SMTEncoding_Term.mkExists _179_1620))
in ((_179_1621), (valid)))
in (FStar_SMTEncoding_Term.mkIff _179_1622))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (_179_1623)))
in (FStar_SMTEncoding_Term.mkForall _179_1624))
in ((_179_1625), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (_179_1626))
in (_179_1627)::[]))))))))))
in (
# 1275 "FStar.SMTEncoding.Encode.fst"
let mk_range_interp = (fun env range tt -> (
# 1276 "FStar.SMTEncoding.Encode.fst"
let range_ty = (FStar_SMTEncoding_Term.mkApp ((range), ([])))
in (let _179_1638 = (let _179_1637 = (let _179_1636 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (let _179_1635 = (let _179_1634 = (varops.mk_unique "typing_range_const")
in Some (_179_1634))
in ((_179_1636), (Some ("Range_const typing")), (_179_1635))))
in FStar_SMTEncoding_Term.Assume (_179_1637))
in (_179_1638)::[])))
in (
# 1279 "FStar.SMTEncoding.Encode.fst"
let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _86_1994 -> (match (_86_1994) with
| (l, _86_1993) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_86_1997, f) -> begin
(f env s tt)
end))))))))))))))))))))))

# 1298 "FStar.SMTEncoding.Encode.fst"
let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (
# 1301 "FStar.SMTEncoding.Encode.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1302 "FStar.SMTEncoding.Encode.fst"
let _86_2007 = (encode_function_type_as_formula None None t env)
in (match (_86_2007) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))

# 1303 "FStar.SMTEncoding.Encode.fst"
let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (
# 1306 "FStar.SMTEncoding.Encode.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _179_1837 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _179_1837)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(
# 1309 "FStar.SMTEncoding.Encode.fst"
let _86_2017 = (new_term_constant_and_tok_from_lid env lid)
in (match (_86_2017) with
| (vname, vtok, env) -> begin
(
# 1310 "FStar.SMTEncoding.Encode.fst"
let arg_sorts = (match ((let _179_1838 = (FStar_Syntax_Subst.compress t_norm)
in _179_1838.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _86_2020) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _86_2023 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _86_2026 -> begin
[]
end)
in (
# 1313 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (
# 1314 "FStar.SMTEncoding.Encode.fst"
let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env)))))
end))
end else begin
if (prims.is lid) then begin
(
# 1317 "FStar.SMTEncoding.Encode.fst"
let vname = (varops.new_fvar lid)
in (
# 1318 "FStar.SMTEncoding.Encode.fst"
let _86_2033 = (prims.mk lid vname)
in (match (_86_2033) with
| (tok, definition) -> begin
(
# 1319 "FStar.SMTEncoding.Encode.fst"
let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end else begin
(
# 1321 "FStar.SMTEncoding.Encode.fst"
let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (
# 1322 "FStar.SMTEncoding.Encode.fst"
let _86_2043 = (
# 1323 "FStar.SMTEncoding.Encode.fst"
let _86_2038 = (curried_arrow_formals_comp t_norm)
in (match (_86_2038) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _179_1840 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (_179_1840)))
end else begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end
end))
in (match (_86_2043) with
| (formals, (pre_opt, res_t)) -> begin
(
# 1327 "FStar.SMTEncoding.Encode.fst"
let _86_2047 = (new_term_constant_and_tok_from_lid env lid)
in (match (_86_2047) with
| (vname, vtok, env) -> begin
(
# 1328 "FStar.SMTEncoding.Encode.fst"
let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| _86_2050 -> begin
(FStar_SMTEncoding_Term.mkApp ((vtok), ([])))
end)
in (
# 1331 "FStar.SMTEncoding.Encode.fst"
let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _86_14 -> (match (_86_14) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(
# 1333 "FStar.SMTEncoding.Encode.fst"
let _86_2066 = (FStar_Util.prefix vars)
in (match (_86_2066) with
| (_86_2061, (xxsym, _86_2064)) -> begin
(
# 1334 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (let _179_1857 = (let _179_1856 = (let _179_1855 = (let _179_1854 = (let _179_1853 = (let _179_1852 = (let _179_1851 = (let _179_1850 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _179_1850))
in ((vapp), (_179_1851)))
in (FStar_SMTEncoding_Term.mkEq _179_1852))
in ((((vapp)::[])::[]), (vars), (_179_1853)))
in (FStar_SMTEncoding_Term.mkForall _179_1854))
in ((_179_1855), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (_179_1856))
in (_179_1857)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(
# 1341 "FStar.SMTEncoding.Encode.fst"
let _86_2078 = (FStar_Util.prefix vars)
in (match (_86_2078) with
| (_86_2073, (xxsym, _86_2076)) -> begin
(
# 1342 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (
# 1343 "FStar.SMTEncoding.Encode.fst"
let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (
# 1344 "FStar.SMTEncoding.Encode.fst"
let tp_name = (mk_term_projector_name d f)
in (
# 1345 "FStar.SMTEncoding.Encode.fst"
let prim_app = (FStar_SMTEncoding_Term.mkApp ((tp_name), ((xx)::[])))
in (let _179_1862 = (let _179_1861 = (let _179_1860 = (let _179_1859 = (let _179_1858 = (FStar_SMTEncoding_Term.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (_179_1858)))
in (FStar_SMTEncoding_Term.mkForall _179_1859))
in ((_179_1860), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (_179_1861))
in (_179_1862)::[])))))
end))
end
| _86_2084 -> begin
[]
end)))))
in (
# 1349 "FStar.SMTEncoding.Encode.fst"
let _86_2091 = (encode_binders None formals env)
in (match (_86_2091) with
| (vars, guards, env', decls1, _86_2090) -> begin
(
# 1350 "FStar.SMTEncoding.Encode.fst"
let _86_2100 = (match (pre_opt) with
| None -> begin
(let _179_1863 = (FStar_SMTEncoding_Term.mk_and_l guards)
in ((_179_1863), (decls1)))
end
| Some (p) -> begin
(
# 1352 "FStar.SMTEncoding.Encode.fst"
let _86_2097 = (encode_formula p env')
in (match (_86_2097) with
| (g, ds) -> begin
(let _179_1864 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in ((_179_1864), ((FStar_List.append decls1 ds))))
end))
end)
in (match (_86_2100) with
| (guard, decls1) -> begin
(
# 1353 "FStar.SMTEncoding.Encode.fst"
let vtok_app = (mk_Apply vtok_tm vars)
in (
# 1355 "FStar.SMTEncoding.Encode.fst"
let vapp = (let _179_1866 = (let _179_1865 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((vname), (_179_1865)))
in (FStar_SMTEncoding_Term.mkApp _179_1866))
in (
# 1356 "FStar.SMTEncoding.Encode.fst"
let _86_2124 = (
# 1357 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _179_1869 = (let _179_1868 = (FStar_All.pipe_right formals (FStar_List.map (fun _86_2103 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (_179_1868), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_179_1869))
in (
# 1358 "FStar.SMTEncoding.Encode.fst"
let _86_2111 = (
# 1359 "FStar.SMTEncoding.Encode.fst"
let env = (
# 1359 "FStar.SMTEncoding.Encode.fst"
let _86_2106 = env
in {bindings = _86_2106.bindings; depth = _86_2106.depth; tcenv = _86_2106.tcenv; warn = _86_2106.warn; cache = _86_2106.cache; nolabels = _86_2106.nolabels; use_zfuel_name = _86_2106.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_86_2111) with
| (tok_typing, decls2) -> begin
(
# 1363 "FStar.SMTEncoding.Encode.fst"
let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (
# 1364 "FStar.SMTEncoding.Encode.fst"
let _86_2121 = (match (formals) with
| [] -> begin
(let _179_1873 = (let _179_1872 = (let _179_1871 = (FStar_SMTEncoding_Term.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _179_1870 -> Some (_179_1870)) _179_1871))
in (push_free_var env lid vname _179_1872))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (_179_1873)))
end
| _86_2115 -> begin
(
# 1367 "FStar.SMTEncoding.Encode.fst"
let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (
# 1368 "FStar.SMTEncoding.Encode.fst"
let vtok_fresh = (let _179_1874 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) _179_1874))
in (
# 1369 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _179_1878 = (let _179_1877 = (let _179_1876 = (let _179_1875 = (FStar_SMTEncoding_Term.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (_179_1875)))
in (FStar_SMTEncoding_Term.mkForall _179_1876))
in ((_179_1877), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (_179_1878))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (_86_2121) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (_86_2124) with
| (decls2, env) -> begin
(
# 1374 "FStar.SMTEncoding.Encode.fst"
let _86_2132 = (
# 1375 "FStar.SMTEncoding.Encode.fst"
let res_t = (FStar_Syntax_Subst.compress res_t)
in (
# 1376 "FStar.SMTEncoding.Encode.fst"
let _86_2128 = (encode_term res_t env')
in (match (_86_2128) with
| (encoded_res_t, decls) -> begin
(let _179_1879 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (_179_1879), (decls)))
end)))
in (match (_86_2132) with
| (encoded_res_t, ty_pred, decls3) -> begin
(
# 1378 "FStar.SMTEncoding.Encode.fst"
let typingAx = (let _179_1883 = (let _179_1882 = (let _179_1881 = (let _179_1880 = (FStar_SMTEncoding_Term.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (_179_1880)))
in (FStar_SMTEncoding_Term.mkForall _179_1881))
in ((_179_1882), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (_179_1883))
in (
# 1381 "FStar.SMTEncoding.Encode.fst"
let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _179_1889 = (let _179_1886 = (let _179_1885 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _179_1884 = (varops.next_id ())
in ((vname), (_179_1885), (FStar_SMTEncoding_Term.Term_sort), (_179_1884))))
in (FStar_SMTEncoding_Term.fresh_constructor _179_1886))
in (let _179_1888 = (let _179_1887 = (pretype_axiom vapp vars)
in (_179_1887)::[])
in (_179_1889)::_179_1888))
end else begin
[]
end
in (
# 1386 "FStar.SMTEncoding.Encode.fst"
let g = (let _179_1894 = (let _179_1893 = (let _179_1892 = (let _179_1891 = (let _179_1890 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_179_1890)
in (FStar_List.append freshness _179_1891))
in (FStar_List.append decls3 _179_1892))
in (FStar_List.append decls2 _179_1893))
in (FStar_List.append decls1 _179_1894))
in ((g), (env)))))
end))
end))))
end))
end))))
end))
end)))
end
end))

# 1387 "FStar.SMTEncoding.Encode.fst"
let declare_top_level_let : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * FStar_SMTEncoding_Term.term Prims.option) * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (match ((try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(
# 1393 "FStar.SMTEncoding.Encode.fst"
let _86_2143 = (encode_free_var env x t t_norm [])
in (match (_86_2143) with
| (decls, env) -> begin
(
# 1394 "FStar.SMTEncoding.Encode.fst"
let _86_2148 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_86_2148) with
| (n, x', _86_2147) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, _86_2152) -> begin
((((n), (x))), ([]), (env))
end))

# 1397 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (
# 1401 "FStar.SMTEncoding.Encode.fst"
let tt = (norm env t)
in (
# 1407 "FStar.SMTEncoding.Encode.fst"
let _86_2162 = (encode_free_var env lid t tt quals)
in (match (_86_2162) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _179_1912 = (let _179_1911 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _179_1911))
in ((_179_1912), (env)))
end else begin
((decls), (env))
end
end))))

# 1410 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _86_2168 lb -> (match (_86_2168) with
| (decls, env) -> begin
(
# 1414 "FStar.SMTEncoding.Encode.fst"
let _86_2172 = (let _179_1921 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _179_1921 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_86_2172) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))

# 1415 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env _86_2176 quals -> (match (_86_2176) with
| (is_rec, bindings) -> begin
(
# 1418 "FStar.SMTEncoding.Encode.fst"
let eta_expand = (fun binders formals body t -> (
# 1419 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1420 "FStar.SMTEncoding.Encode.fst"
let _86_2186 = (FStar_Util.first_N nbinders formals)
in (match (_86_2186) with
| (formals, extra_formals) -> begin
(
# 1421 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _86_2190 _86_2194 -> (match (((_86_2190), (_86_2194))) with
| ((formal, _86_2189), (binder, _86_2193)) -> begin
(let _179_1939 = (let _179_1938 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (_179_1938)))
in FStar_Syntax_Syntax.NT (_179_1939))
end)) formals binders)
in (
# 1422 "FStar.SMTEncoding.Encode.fst"
let extra_formals = (let _179_1943 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _86_2198 -> (match (_86_2198) with
| (x, i) -> begin
(let _179_1942 = (
# 1422 "FStar.SMTEncoding.Encode.fst"
let _86_2199 = x
in (let _179_1941 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _86_2199.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _86_2199.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _179_1941}))
in ((_179_1942), (i)))
end))))
in (FStar_All.pipe_right _179_1943 FStar_Syntax_Util.name_binders))
in (
# 1423 "FStar.SMTEncoding.Encode.fst"
let body = (let _179_1950 = (FStar_Syntax_Subst.compress body)
in (let _179_1949 = (let _179_1944 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _179_1944))
in (let _179_1948 = (let _179_1947 = (let _179_1946 = (FStar_Syntax_Subst.subst subst t)
in _179_1946.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _179_1945 -> Some (_179_1945)) _179_1947))
in (FStar_Syntax_Syntax.extend_app_n _179_1950 _179_1949 _179_1948 body.FStar_Syntax_Syntax.pos))))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (
# 1426 "FStar.SMTEncoding.Encode.fst"
let destruct_bound_function = (fun flid t_norm e -> (
# 1427 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t_norm -> (match ((let _179_1961 = (FStar_Syntax_Util.unascribe e)
in _179_1961.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(
# 1430 "FStar.SMTEncoding.Encode.fst"
let _86_2218 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_86_2218) with
| (binders, body, opening) -> begin
(match ((let _179_1962 = (FStar_Syntax_Subst.compress t_norm)
in _179_1962.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1433 "FStar.SMTEncoding.Encode.fst"
let _86_2225 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_86_2225) with
| (formals, c) -> begin
(
# 1434 "FStar.SMTEncoding.Encode.fst"
let nformals = (FStar_List.length formals)
in (
# 1435 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1436 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c)) then begin
(
# 1438 "FStar.SMTEncoding.Encode.fst"
let lopt = (subst_lcomp_opt opening lopt)
in (
# 1439 "FStar.SMTEncoding.Encode.fst"
let _86_2232 = (FStar_Util.first_N nformals binders)
in (match (_86_2232) with
| (bs0, rest) -> begin
(
# 1440 "FStar.SMTEncoding.Encode.fst"
let c = (
# 1441 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _86_2236 _86_2240 -> (match (((_86_2236), (_86_2240))) with
| ((b, _86_2235), (x, _86_2239)) -> begin
(let _179_1966 = (let _179_1965 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (_179_1965)))
in FStar_Syntax_Syntax.NT (_179_1966))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (
# 1443 "FStar.SMTEncoding.Encode.fst"
let body = (FStar_Syntax_Util.abs rest body lopt)
in ((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))))
end)))
end else begin
if (nformals > nbinders) then begin
(
# 1446 "FStar.SMTEncoding.Encode.fst"
let _86_2246 = (eta_expand binders formals body tres)
in (match (_86_2246) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end))
end else begin
((binders), (body), (formals), (tres))
end
end)))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, _86_2249) -> begin
(aux norm x.FStar_Syntax_Syntax.sort)
end
| _86_2253 when (not (norm)) -> begin
(
# 1454 "FStar.SMTEncoding.Encode.fst"
let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| _86_2256 -> begin
(let _179_1969 = (let _179_1968 = (FStar_Syntax_Print.term_to_string e)
in (let _179_1967 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _179_1968 _179_1967)))
in (FStar_All.failwith _179_1969))
end)
end))
end
| _86_2258 -> begin
(match ((let _179_1970 = (FStar_Syntax_Subst.compress t_norm)
in _179_1970.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1464 "FStar.SMTEncoding.Encode.fst"
let _86_2265 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_86_2265) with
| (formals, c) -> begin
(
# 1465 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in (
# 1466 "FStar.SMTEncoding.Encode.fst"
let _86_2269 = (eta_expand [] formals e tres)
in (match (_86_2269) with
| (binders, body) -> begin
((binders), (body), (formals), (tres))
end)))
end))
end
| _86_2271 -> begin
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
# 1474 "FStar.SMTEncoding.Encode.fst"
let _86_2299 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _86_2286 lb -> (match (_86_2286) with
| (toks, typs, decls, env) -> begin
(
# 1476 "FStar.SMTEncoding.Encode.fst"
let _86_2288 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (
# 1477 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 1478 "FStar.SMTEncoding.Encode.fst"
let _86_2294 = (let _179_1975 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _179_1975 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_86_2294) with
| (tok, decl, env) -> begin
(let _179_1978 = (let _179_1977 = (let _179_1976 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((_179_1976), (tok)))
in (_179_1977)::toks)
in ((_179_1978), ((t_norm)::typs), ((decl)::decls), (env)))
end))))
end)) (([]), ([]), ([]), (env))))
in (match (_86_2299) with
| (toks, typs, decls, env) -> begin
(
# 1480 "FStar.SMTEncoding.Encode.fst"
let toks = (FStar_List.rev toks)
in (
# 1481 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (
# 1482 "FStar.SMTEncoding.Encode.fst"
let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _86_15 -> (match (_86_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _86_2306 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _179_1981 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _179_1981)))))) then begin
((decls), (env))
end else begin
if (not (is_rec)) then begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = _86_2316; FStar_Syntax_Syntax.lbunivs = _86_2314; FStar_Syntax_Syntax.lbtyp = _86_2312; FStar_Syntax_Syntax.lbeff = _86_2310; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(
# 1489 "FStar.SMTEncoding.Encode.fst"
let e = (FStar_Syntax_Subst.compress e)
in (
# 1490 "FStar.SMTEncoding.Encode.fst"
let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1491 "FStar.SMTEncoding.Encode.fst"
let _86_2336 = (destruct_bound_function flid t_norm e)
in (match (_86_2336) with
| (binders, body, _86_2333, _86_2335) -> begin
(
# 1492 "FStar.SMTEncoding.Encode.fst"
let _86_2343 = (encode_binders None binders env)
in (match (_86_2343) with
| (vars, guards, env', binder_decls, _86_2342) -> begin
(
# 1493 "FStar.SMTEncoding.Encode.fst"
let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
end
| _86_2346 -> begin
(let _179_1983 = (let _179_1982 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((f), (_179_1982)))
in (FStar_SMTEncoding_Term.mkApp _179_1983))
end)
in (
# 1494 "FStar.SMTEncoding.Encode.fst"
let _86_2352 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _179_1985 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _179_1984 = (encode_formula body env')
in ((_179_1985), (_179_1984))))
end else begin
(let _179_1986 = (encode_term body env')
in ((app), (_179_1986)))
end
in (match (_86_2352) with
| (app, (body, decls2)) -> begin
(
# 1500 "FStar.SMTEncoding.Encode.fst"
let eqn = (let _179_1992 = (let _179_1991 = (let _179_1988 = (let _179_1987 = (FStar_SMTEncoding_Term.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (_179_1987)))
in (FStar_SMTEncoding_Term.mkForall _179_1988))
in (let _179_1990 = (let _179_1989 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_179_1989))
in ((_179_1991), (_179_1990), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (_179_1992))
in (let _179_1997 = (let _179_1996 = (let _179_1995 = (let _179_1994 = (let _179_1993 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) _179_1993))
in (FStar_List.append decls2 _179_1994))
in (FStar_List.append binder_decls _179_1995))
in (FStar_List.append decls _179_1996))
in ((_179_1997), (env))))
end)))
end))
end))))
end
| _86_2355 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 1507 "FStar.SMTEncoding.Encode.fst"
let fuel = (let _179_1998 = (varops.fresh "fuel")
in ((_179_1998), (FStar_SMTEncoding_Term.Fuel_sort)))
in (
# 1508 "FStar.SMTEncoding.Encode.fst"
let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (
# 1509 "FStar.SMTEncoding.Encode.fst"
let env0 = env
in (
# 1510 "FStar.SMTEncoding.Encode.fst"
let _86_2373 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _86_2361 _86_2366 -> (match (((_86_2361), (_86_2366))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(
# 1511 "FStar.SMTEncoding.Encode.fst"
let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1512 "FStar.SMTEncoding.Encode.fst"
let g = (let _179_2001 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar _179_2001))
in (
# 1513 "FStar.SMTEncoding.Encode.fst"
let gtok = (let _179_2002 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar _179_2002))
in (
# 1514 "FStar.SMTEncoding.Encode.fst"
let env = (let _179_2005 = (let _179_2004 = (FStar_SMTEncoding_Term.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _179_2003 -> Some (_179_2003)) _179_2004))
in (push_free_var env flid gtok _179_2005))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (_86_2373) with
| (gtoks, env) -> begin
(
# 1516 "FStar.SMTEncoding.Encode.fst"
let gtoks = (FStar_List.rev gtoks)
in (
# 1517 "FStar.SMTEncoding.Encode.fst"
let encode_one_binding = (fun env0 _86_2382 t_norm _86_2393 -> (match (((_86_2382), (_86_2393))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _86_2392; FStar_Syntax_Syntax.lbunivs = _86_2390; FStar_Syntax_Syntax.lbtyp = _86_2388; FStar_Syntax_Syntax.lbeff = _86_2386; FStar_Syntax_Syntax.lbdef = e}) -> begin
(
# 1518 "FStar.SMTEncoding.Encode.fst"
let _86_2398 = (destruct_bound_function flid t_norm e)
in (match (_86_2398) with
| (binders, body, formals, tres) -> begin
(
# 1519 "FStar.SMTEncoding.Encode.fst"
let _86_2405 = (encode_binders None binders env)
in (match (_86_2405) with
| (vars, guards, env', binder_decls, _86_2404) -> begin
(
# 1520 "FStar.SMTEncoding.Encode.fst"
let decl_g = (let _179_2016 = (let _179_2015 = (let _179_2014 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_179_2014)
in ((g), (_179_2015), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (_179_2016))
in (
# 1521 "FStar.SMTEncoding.Encode.fst"
let env0 = (push_zfuel_name env0 flid g)
in (
# 1522 "FStar.SMTEncoding.Encode.fst"
let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (
# 1523 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1524 "FStar.SMTEncoding.Encode.fst"
let app = (FStar_SMTEncoding_Term.mkApp ((f), (vars_tm)))
in (
# 1525 "FStar.SMTEncoding.Encode.fst"
let gsapp = (let _179_2019 = (let _179_2018 = (let _179_2017 = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (_179_2017)::vars_tm)
in ((g), (_179_2018)))
in (FStar_SMTEncoding_Term.mkApp _179_2019))
in (
# 1526 "FStar.SMTEncoding.Encode.fst"
let gmax = (let _179_2022 = (let _179_2021 = (let _179_2020 = (FStar_SMTEncoding_Term.mkApp (("MaxFuel"), ([])))
in (_179_2020)::vars_tm)
in ((g), (_179_2021)))
in (FStar_SMTEncoding_Term.mkApp _179_2022))
in (
# 1527 "FStar.SMTEncoding.Encode.fst"
let _86_2415 = (encode_term body env')
in (match (_86_2415) with
| (body_tm, decls2) -> begin
(
# 1531 "FStar.SMTEncoding.Encode.fst"
let eqn_g = (let _179_2028 = (let _179_2027 = (let _179_2024 = (let _179_2023 = (FStar_SMTEncoding_Term.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some (0)), ((fuel)::vars), (_179_2023)))
in (FStar_SMTEncoding_Term.mkForall' _179_2024))
in (let _179_2026 = (let _179_2025 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_179_2025))
in ((_179_2027), (_179_2026), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (_179_2028))
in (
# 1534 "FStar.SMTEncoding.Encode.fst"
let eqn_f = (let _179_2032 = (let _179_2031 = (let _179_2030 = (let _179_2029 = (FStar_SMTEncoding_Term.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (_179_2029)))
in (FStar_SMTEncoding_Term.mkForall _179_2030))
in ((_179_2031), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_179_2032))
in (
# 1537 "FStar.SMTEncoding.Encode.fst"
let eqn_g' = (let _179_2041 = (let _179_2040 = (let _179_2039 = (let _179_2038 = (let _179_2037 = (let _179_2036 = (let _179_2035 = (let _179_2034 = (let _179_2033 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_179_2033)::vars_tm)
in ((g), (_179_2034)))
in (FStar_SMTEncoding_Term.mkApp _179_2035))
in ((gsapp), (_179_2036)))
in (FStar_SMTEncoding_Term.mkEq _179_2037))
in ((((gsapp)::[])::[]), ((fuel)::vars), (_179_2038)))
in (FStar_SMTEncoding_Term.mkForall _179_2039))
in ((_179_2040), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (_179_2041))
in (
# 1540 "FStar.SMTEncoding.Encode.fst"
let _86_2438 = (
# 1541 "FStar.SMTEncoding.Encode.fst"
let _86_2425 = (encode_binders None formals env0)
in (match (_86_2425) with
| (vars, v_guards, env, binder_decls, _86_2424) -> begin
(
# 1542 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1543 "FStar.SMTEncoding.Encode.fst"
let gapp = (FStar_SMTEncoding_Term.mkApp ((g), ((fuel_tm)::vars_tm)))
in (
# 1544 "FStar.SMTEncoding.Encode.fst"
let tok_corr = (
# 1545 "FStar.SMTEncoding.Encode.fst"
let tok_app = (let _179_2042 = (FStar_SMTEncoding_Term.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply _179_2042 ((fuel)::vars)))
in (let _179_2046 = (let _179_2045 = (let _179_2044 = (let _179_2043 = (FStar_SMTEncoding_Term.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (_179_2043)))
in (FStar_SMTEncoding_Term.mkForall _179_2044))
in ((_179_2045), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (_179_2046)))
in (
# 1549 "FStar.SMTEncoding.Encode.fst"
let _86_2435 = (
# 1550 "FStar.SMTEncoding.Encode.fst"
let _86_2432 = (encode_term_pred None tres env gapp)
in (match (_86_2432) with
| (g_typing, d3) -> begin
(let _179_2054 = (let _179_2053 = (let _179_2052 = (let _179_2051 = (let _179_2050 = (let _179_2049 = (let _179_2048 = (let _179_2047 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in ((_179_2047), (g_typing)))
in (FStar_SMTEncoding_Term.mkImp _179_2048))
in ((((gapp)::[])::[]), ((fuel)::vars), (_179_2049)))
in (FStar_SMTEncoding_Term.mkForall _179_2050))
in ((_179_2051), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (_179_2052))
in (_179_2053)::[])
in ((d3), (_179_2054)))
end))
in (match (_86_2435) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (_86_2438) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end))
end))
end))
in (
# 1556 "FStar.SMTEncoding.Encode.fst"
let _86_2454 = (let _179_2057 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _86_2442 _86_2446 -> (match (((_86_2442), (_86_2446))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(
# 1557 "FStar.SMTEncoding.Encode.fst"
let _86_2450 = (encode_one_binding env0 gtok ty bs)
in (match (_86_2450) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) _179_2057))
in (match (_86_2454) with
| (decls, eqns, env0) -> begin
(
# 1559 "FStar.SMTEncoding.Encode.fst"
let _86_2463 = (let _179_2059 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _179_2059 (FStar_List.partition (fun _86_16 -> (match (_86_16) with
| FStar_SMTEncoding_Term.DeclFun (_86_2457) -> begin
true
end
| _86_2460 -> begin
false
end)))))
in (match (_86_2463) with
| (prefix_decls, rest) -> begin
(
# 1562 "FStar.SMTEncoding.Encode.fst"
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
# 1565 "FStar.SMTEncoding.Encode.fst"
let msg = (let _179_2062 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _179_2062 (FStar_String.concat " and ")))
in (
# 1566 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))

# 1567 "FStar.SMTEncoding.Encode.fst"
let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1570 "FStar.SMTEncoding.Encode.fst"
let _86_2467 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _179_2071 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _179_2071))
end else begin
()
end
in (
# 1573 "FStar.SMTEncoding.Encode.fst"
let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (
# 1576 "FStar.SMTEncoding.Encode.fst"
let _86_2475 = (encode_sigelt' env se)
in (match (_86_2475) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _179_2074 = (let _179_2073 = (let _179_2072 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_179_2072))
in (_179_2073)::[])
in ((_179_2074), (e)))
end
| _86_2478 -> begin
(let _179_2081 = (let _179_2080 = (let _179_2076 = (let _179_2075 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_179_2075))
in (_179_2076)::g)
in (let _179_2079 = (let _179_2078 = (let _179_2077 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_179_2077))
in (_179_2078)::[])
in (FStar_List.append _179_2080 _179_2079)))
in ((_179_2081), (e)))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1582 "FStar.SMTEncoding.Encode.fst"
let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (_86_2484) -> begin
(FStar_All.failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, _86_2500) -> begin
if (let _179_2086 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right _179_2086 Prims.op_Negation)) then begin
(([]), (env))
end else begin
(
# 1610 "FStar.SMTEncoding.Encode.fst"
let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| _86_2507 -> begin
(let _179_2092 = (let _179_2091 = (let _179_2090 = (FStar_All.pipe_left (fun _179_2089 -> Some (_179_2089)) (FStar_Util.Inr (FStar_Syntax_Const.effect_Tot_lid)))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (_179_2090)))
in FStar_Syntax_Syntax.Tm_abs (_179_2091))
in (FStar_Syntax_Syntax.mk _179_2092 None tm.FStar_Syntax_Syntax.pos))
end))
in (
# 1616 "FStar.SMTEncoding.Encode.fst"
let encode_action = (fun env a -> (
# 1617 "FStar.SMTEncoding.Encode.fst"
let _86_2514 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (_86_2514) with
| (aname, atok, env) -> begin
(
# 1618 "FStar.SMTEncoding.Encode.fst"
let _86_2518 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (_86_2518) with
| (formals, _86_2517) -> begin
(
# 1619 "FStar.SMTEncoding.Encode.fst"
let _86_2521 = (let _179_2097 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term _179_2097 env))
in (match (_86_2521) with
| (tm, decls) -> begin
(
# 1620 "FStar.SMTEncoding.Encode.fst"
let a_decls = (let _179_2101 = (let _179_2100 = (let _179_2099 = (FStar_All.pipe_right formals (FStar_List.map (fun _86_2522 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (_179_2099), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (_179_2100))
in (_179_2101)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (
# 1623 "FStar.SMTEncoding.Encode.fst"
let _86_2536 = (let _179_2103 = (FStar_All.pipe_right formals (FStar_List.map (fun _86_2528 -> (match (_86_2528) with
| (bv, _86_2527) -> begin
(
# 1623 "FStar.SMTEncoding.Encode.fst"
let _86_2533 = (gen_term_var env bv)
in (match (_86_2533) with
| (xxsym, xx, _86_2532) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right _179_2103 FStar_List.split))
in (match (_86_2536) with
| (xs_sorts, xs) -> begin
(
# 1624 "FStar.SMTEncoding.Encode.fst"
let app = (let _179_2107 = (let _179_2106 = (let _179_2105 = (let _179_2104 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Var (aname)), (xs)))))
in (_179_2104)::[])
in ((FStar_SMTEncoding_Term.Var ("Reify")), (_179_2105)))
in FStar_SMTEncoding_Term.App (_179_2106))
in (FStar_All.pipe_right _179_2107 FStar_SMTEncoding_Term.mk))
in (
# 1625 "FStar.SMTEncoding.Encode.fst"
let a_eq = (let _179_2113 = (let _179_2112 = (let _179_2111 = (let _179_2110 = (let _179_2109 = (let _179_2108 = (mk_Apply tm xs_sorts)
in ((app), (_179_2108)))
in (FStar_SMTEncoding_Term.mkEq _179_2109))
in ((((app)::[])::[]), (xs_sorts), (_179_2110)))
in (FStar_SMTEncoding_Term.mkForall _179_2111))
in ((_179_2112), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (_179_2113))
in (
# 1628 "FStar.SMTEncoding.Encode.fst"
let tok_correspondence = (
# 1629 "FStar.SMTEncoding.Encode.fst"
let tok_term = (FStar_SMTEncoding_Term.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (
# 1630 "FStar.SMTEncoding.Encode.fst"
let tok_app = (mk_Apply tok_term xs_sorts)
in (let _179_2117 = (let _179_2116 = (let _179_2115 = (let _179_2114 = (FStar_SMTEncoding_Term.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (_179_2114)))
in (FStar_SMTEncoding_Term.mkForall _179_2115))
in ((_179_2116), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (_179_2117))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (
# 1636 "FStar.SMTEncoding.Encode.fst"
let _86_2544 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (_86_2544) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _86_2547, _86_2549, _86_2551, _86_2553) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(
# 1640 "FStar.SMTEncoding.Encode.fst"
let _86_2559 = (new_term_constant_and_tok_from_lid env lid)
in (match (_86_2559) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _86_2562, t, quals, _86_2566) -> begin
(
# 1644 "FStar.SMTEncoding.Encode.fst"
let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _86_17 -> (match (_86_17) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _86_2579 -> begin
false
end))))))
in if will_encode_definition then begin
(([]), (env))
end else begin
(
# 1649 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (
# 1650 "FStar.SMTEncoding.Encode.fst"
let _86_2584 = (encode_top_level_val env fv t quals)
in (match (_86_2584) with
| (decls, env) -> begin
(
# 1651 "FStar.SMTEncoding.Encode.fst"
let tname = lid.FStar_Ident.str
in (
# 1652 "FStar.SMTEncoding.Encode.fst"
let tsym = (FStar_SMTEncoding_Term.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (let _179_2120 = (let _179_2119 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _179_2119))
in ((_179_2120), (env)))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _86_2590, _86_2592) -> begin
(
# 1658 "FStar.SMTEncoding.Encode.fst"
let _86_2597 = (encode_formula f env)
in (match (_86_2597) with
| (f, decls) -> begin
(
# 1659 "FStar.SMTEncoding.Encode.fst"
let g = (let _179_2127 = (let _179_2126 = (let _179_2125 = (let _179_2122 = (let _179_2121 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _179_2121))
in Some (_179_2122))
in (let _179_2124 = (let _179_2123 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (_179_2123))
in ((f), (_179_2125), (_179_2124))))
in FStar_SMTEncoding_Term.Assume (_179_2126))
in (_179_2127)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _86_2602, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(
# 1663 "FStar.SMTEncoding.Encode.fst"
let _86_2615 = (FStar_Util.fold_map (fun env lb -> (
# 1664 "FStar.SMTEncoding.Encode.fst"
let lid = (let _179_2131 = (let _179_2130 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in _179_2130.FStar_Syntax_Syntax.fv_name)
in _179_2131.FStar_Syntax_Syntax.v)
in if (let _179_2132 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone _179_2132)) then begin
(
# 1666 "FStar.SMTEncoding.Encode.fst"
let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (
# 1667 "FStar.SMTEncoding.Encode.fst"
let _86_2612 = (encode_sigelt' env val_decl)
in (match (_86_2612) with
| (decls, env) -> begin
((env), (decls))
end)))
end else begin
((env), ([]))
end)) env (Prims.snd lbs))
in (match (_86_2615) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((_86_2617, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _86_2625; FStar_Syntax_Syntax.lbtyp = _86_2623; FStar_Syntax_Syntax.lbeff = _86_2621; FStar_Syntax_Syntax.lbdef = _86_2619})::[]), _86_2632, _86_2634, _86_2636) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(
# 1673 "FStar.SMTEncoding.Encode.fst"
let _86_2642 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_86_2642) with
| (tname, ttok, env) -> begin
(
# 1674 "FStar.SMTEncoding.Encode.fst"
let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (
# 1675 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1676 "FStar.SMTEncoding.Encode.fst"
let valid_b2t_x = (let _179_2135 = (let _179_2134 = (let _179_2133 = (FStar_SMTEncoding_Term.mkApp (("Prims.b2t"), ((x)::[])))
in (_179_2133)::[])
in (("Valid"), (_179_2134)))
in (FStar_SMTEncoding_Term.mkApp _179_2135))
in (
# 1677 "FStar.SMTEncoding.Encode.fst"
let decls = (let _179_2143 = (let _179_2142 = (let _179_2141 = (let _179_2140 = (let _179_2139 = (let _179_2138 = (let _179_2137 = (let _179_2136 = (FStar_SMTEncoding_Term.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (_179_2136)))
in (FStar_SMTEncoding_Term.mkEq _179_2137))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (_179_2138)))
in (FStar_SMTEncoding_Term.mkForall _179_2139))
in ((_179_2140), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (_179_2141))
in (_179_2142)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::_179_2143)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_86_2648, _86_2650, _86_2652, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _86_18 -> (match (_86_18) with
| FStar_Syntax_Syntax.Discriminator (_86_2658) -> begin
true
end
| _86_2661 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (_86_2663, _86_2665, lids, quals) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> ((let _179_2146 = (FStar_List.hd l.FStar_Ident.ns)
in _179_2146.FStar_Ident.idText) = "Prims")))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun _86_19 -> (match (_86_19) with
| FStar_Syntax_Syntax.Inline -> begin
true
end
| _86_2674 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _86_2680, _86_2682, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _86_20 -> (match (_86_20) with
| FStar_Syntax_Syntax.Projector (_86_2688) -> begin
true
end
| _86_2691 -> begin
false
end)))) -> begin
(
# 1696 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 1697 "FStar.SMTEncoding.Encode.fst"
let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_86_2695) -> begin
(([]), (env))
end
| None -> begin
(
# 1702 "FStar.SMTEncoding.Encode.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), _86_2704, _86_2706, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(match ((let _179_2149 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in _179_2149.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, _86_2713) -> begin
(
# 1709 "FStar.SMTEncoding.Encode.fst"
let body = (FStar_Syntax_Util.mk_reify body)
in (
# 1710 "FStar.SMTEncoding.Encode.fst"
let tm = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None)))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (
# 1711 "FStar.SMTEncoding.Encode.fst"
let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (
# 1712 "FStar.SMTEncoding.Encode.fst"
let lb_typ = (
# 1713 "FStar.SMTEncoding.Encode.fst"
let _86_2721 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (_86_2721) with
| (formals, comp) -> begin
(
# 1714 "FStar.SMTEncoding.Encode.fst"
let reified_typ = (FStar_TypeChecker_Util.reify_comp (
# 1714 "FStar.SMTEncoding.Encode.fst"
let _86_2722 = env.tcenv
in {FStar_TypeChecker_Env.solver = _86_2722.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _86_2722.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _86_2722.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _86_2722.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _86_2722.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _86_2722.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _86_2722.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _86_2722.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _86_2722.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _86_2722.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _86_2722.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _86_2722.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _86_2722.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _86_2722.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _86_2722.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _86_2722.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _86_2722.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _86_2722.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.type_of = _86_2722.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = _86_2722.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = _86_2722.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = _86_2722.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (let _179_2150 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals _179_2150)))
end))
in (
# 1716 "FStar.SMTEncoding.Encode.fst"
let lb = (
# 1716 "FStar.SMTEncoding.Encode.fst"
let _86_2726 = lb
in {FStar_Syntax_Syntax.lbname = _86_2726.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = _86_2726.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = _86_2726.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in (encode_top_level_let env ((false), ((lb)::[])) quals))))))
end
| _86_2730 -> begin
(([]), (env))
end)
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _86_2735, _86_2737, quals) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _86_2743, _86_2745, _86_2747) -> begin
(
# 1729 "FStar.SMTEncoding.Encode.fst"
let _86_2752 = (encode_signature env ses)
in (match (_86_2752) with
| (g, env) -> begin
(
# 1730 "FStar.SMTEncoding.Encode.fst"
let _86_2766 = (FStar_All.pipe_right g (FStar_List.partition (fun _86_21 -> (match (_86_21) with
| FStar_SMTEncoding_Term.Assume (_86_2755, Some ("inversion axiom"), _86_2759) -> begin
false
end
| _86_2763 -> begin
true
end))))
in (match (_86_2766) with
| (g', inversions) -> begin
(
# 1733 "FStar.SMTEncoding.Encode.fst"
let _86_2775 = (FStar_All.pipe_right g' (FStar_List.partition (fun _86_22 -> (match (_86_22) with
| FStar_SMTEncoding_Term.DeclFun (_86_2769) -> begin
true
end
| _86_2772 -> begin
false
end))))
in (match (_86_2775) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _86_2778, tps, k, _86_2782, datas, quals, _86_2786) -> begin
(
# 1739 "FStar.SMTEncoding.Encode.fst"
let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _86_23 -> (match (_86_23) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _86_2793 -> begin
false
end))))
in (
# 1740 "FStar.SMTEncoding.Encode.fst"
let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(
# 1742 "FStar.SMTEncoding.Encode.fst"
let _86_2805 = c
in (match (_86_2805) with
| (name, args, _86_2800, _86_2802, _86_2804) -> begin
(let _179_2158 = (let _179_2157 = (let _179_2156 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (_179_2156), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (_179_2157))
in (_179_2158)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (
# 1746 "FStar.SMTEncoding.Encode.fst"
let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _179_2164 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _179_2164 FStar_Option.isNone))))) then begin
[]
end else begin
(
# 1750 "FStar.SMTEncoding.Encode.fst"
let _86_2812 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_86_2812) with
| (xxsym, xx) -> begin
(
# 1751 "FStar.SMTEncoding.Encode.fst"
let _86_2848 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _86_2815 l -> (match (_86_2815) with
| (out, decls) -> begin
(
# 1752 "FStar.SMTEncoding.Encode.fst"
let _86_2820 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_86_2820) with
| (_86_2818, data_t) -> begin
(
# 1753 "FStar.SMTEncoding.Encode.fst"
let _86_2823 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_86_2823) with
| (args, res) -> begin
(
# 1754 "FStar.SMTEncoding.Encode.fst"
let indices = (match ((let _179_2167 = (FStar_Syntax_Subst.compress res)
in _179_2167.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_86_2825, indices) -> begin
indices
end
| _86_2830 -> begin
[]
end)
in (
# 1757 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _86_2836 -> (match (_86_2836) with
| (x, _86_2835) -> begin
(let _179_2172 = (let _179_2171 = (let _179_2170 = (mk_term_projector_name l x)
in ((_179_2170), ((xx)::[])))
in (FStar_SMTEncoding_Term.mkApp _179_2171))
in (push_term_var env x _179_2172))
end)) env))
in (
# 1760 "FStar.SMTEncoding.Encode.fst"
let _86_2840 = (encode_args indices env)
in (match (_86_2840) with
| (indices, decls') -> begin
(
# 1761 "FStar.SMTEncoding.Encode.fst"
let _86_2841 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (
# 1763 "FStar.SMTEncoding.Encode.fst"
let eqs = (let _179_2177 = (FStar_List.map2 (fun v a -> (let _179_2176 = (let _179_2175 = (FStar_SMTEncoding_Term.mkFreeV v)
in ((_179_2175), (a)))
in (FStar_SMTEncoding_Term.mkEq _179_2176))) vars indices)
in (FStar_All.pipe_right _179_2177 FStar_SMTEncoding_Term.mk_and_l))
in (let _179_2182 = (let _179_2181 = (let _179_2180 = (let _179_2179 = (let _179_2178 = (mk_data_tester env l xx)
in ((_179_2178), (eqs)))
in (FStar_SMTEncoding_Term.mkAnd _179_2179))
in ((out), (_179_2180)))
in (FStar_SMTEncoding_Term.mkOr _179_2181))
in ((_179_2182), ((FStar_List.append decls decls'))))))
end))))
end))
end))
end)) ((FStar_SMTEncoding_Term.mkFalse), ([]))))
in (match (_86_2848) with
| (data_ax, decls) -> begin
(
# 1765 "FStar.SMTEncoding.Encode.fst"
let _86_2851 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_86_2851) with
| (ffsym, ff) -> begin
(
# 1766 "FStar.SMTEncoding.Encode.fst"
let fuel_guarded_inversion = (
# 1767 "FStar.SMTEncoding.Encode.fst"
let xx_has_type_sfuel = if ((FStar_List.length datas) > 1) then begin
(let _179_2183 = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _179_2183 xx tapp))
end else begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end
in (let _179_2190 = (let _179_2189 = (let _179_2186 = (let _179_2185 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _179_2184 = (FStar_SMTEncoding_Term.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (_179_2185), (_179_2184))))
in (FStar_SMTEncoding_Term.mkForall _179_2186))
in (let _179_2188 = (let _179_2187 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (_179_2187))
in ((_179_2189), (Some ("inversion axiom")), (_179_2188))))
in FStar_SMTEncoding_Term.Assume (_179_2190)))
in (
# 1775 "FStar.SMTEncoding.Encode.fst"
let pattern_guarded_inversion = if ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > 1)) then begin
(
# 1778 "FStar.SMTEncoding.Encode.fst"
let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (
# 1779 "FStar.SMTEncoding.Encode.fst"
let pattern_guard = (FStar_SMTEncoding_Term.mkApp (("Prims.inversion"), ((tapp)::[])))
in (let _179_2198 = (let _179_2197 = (let _179_2196 = (let _179_2193 = (let _179_2192 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (let _179_2191 = (FStar_SMTEncoding_Term.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (_179_2192), (_179_2191))))
in (FStar_SMTEncoding_Term.mkForall _179_2193))
in (let _179_2195 = (let _179_2194 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (_179_2194))
in ((_179_2196), (Some ("inversion axiom")), (_179_2195))))
in FStar_SMTEncoding_Term.Assume (_179_2197))
in (_179_2198)::[])))
end else begin
[]
end
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)
in (
# 1789 "FStar.SMTEncoding.Encode.fst"
let _86_2865 = (match ((let _179_2199 = (FStar_Syntax_Subst.compress k)
in _179_2199.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| _86_2862 -> begin
((tps), (k))
end)
in (match (_86_2865) with
| (formals, res) -> begin
(
# 1795 "FStar.SMTEncoding.Encode.fst"
let _86_2868 = (FStar_Syntax_Subst.open_term formals res)
in (match (_86_2868) with
| (formals, res) -> begin
(
# 1796 "FStar.SMTEncoding.Encode.fst"
let _86_2875 = (encode_binders None formals env)
in (match (_86_2875) with
| (vars, guards, env', binder_decls, _86_2874) -> begin
(
# 1798 "FStar.SMTEncoding.Encode.fst"
let _86_2879 = (new_term_constant_and_tok_from_lid env t)
in (match (_86_2879) with
| (tname, ttok, env) -> begin
(
# 1799 "FStar.SMTEncoding.Encode.fst"
let ttok_tm = (FStar_SMTEncoding_Term.mkApp ((ttok), ([])))
in (
# 1800 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1801 "FStar.SMTEncoding.Encode.fst"
let tapp = (let _179_2201 = (let _179_2200 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in ((tname), (_179_2200)))
in (FStar_SMTEncoding_Term.mkApp _179_2201))
in (
# 1802 "FStar.SMTEncoding.Encode.fst"
let _86_2900 = (
# 1803 "FStar.SMTEncoding.Encode.fst"
let tname_decl = (let _179_2205 = (let _179_2204 = (FStar_All.pipe_right vars (FStar_List.map (fun _86_2885 -> (match (_86_2885) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (let _179_2203 = (varops.next_id ())
in ((tname), (_179_2204), (FStar_SMTEncoding_Term.Term_sort), (_179_2203), (false))))
in (constructor_or_logic_type_decl _179_2205))
in (
# 1804 "FStar.SMTEncoding.Encode.fst"
let _86_2897 = (match (vars) with
| [] -> begin
(let _179_2209 = (let _179_2208 = (let _179_2207 = (FStar_SMTEncoding_Term.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _179_2206 -> Some (_179_2206)) _179_2207))
in (push_free_var env t tname _179_2208))
in (([]), (_179_2209)))
end
| _86_2889 -> begin
(
# 1807 "FStar.SMTEncoding.Encode.fst"
let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (
# 1808 "FStar.SMTEncoding.Encode.fst"
let ttok_fresh = (let _179_2210 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) _179_2210))
in (
# 1809 "FStar.SMTEncoding.Encode.fst"
let ttok_app = (mk_Apply ttok_tm vars)
in (
# 1810 "FStar.SMTEncoding.Encode.fst"
let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (
# 1813 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _179_2214 = (let _179_2213 = (let _179_2212 = (let _179_2211 = (FStar_SMTEncoding_Term.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (_179_2211)))
in (FStar_SMTEncoding_Term.mkForall' _179_2212))
in ((_179_2213), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_179_2214))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (_86_2897) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (_86_2900) with
| (decls, env) -> begin
(
# 1818 "FStar.SMTEncoding.Encode.fst"
let kindingAx = (
# 1819 "FStar.SMTEncoding.Encode.fst"
let _86_2903 = (encode_term_pred None res env' tapp)
in (match (_86_2903) with
| (k, decls) -> begin
(
# 1820 "FStar.SMTEncoding.Encode.fst"
let karr = if ((FStar_List.length formals) > 0) then begin
(let _179_2218 = (let _179_2217 = (let _179_2216 = (let _179_2215 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _179_2215))
in ((_179_2216), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_179_2217))
in (_179_2218)::[])
end else begin
[]
end
in (let _179_2225 = (let _179_2224 = (let _179_2223 = (let _179_2222 = (let _179_2221 = (let _179_2220 = (let _179_2219 = (FStar_SMTEncoding_Term.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (_179_2219)))
in (FStar_SMTEncoding_Term.mkForall _179_2220))
in ((_179_2221), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (_179_2222))
in (_179_2223)::[])
in (FStar_List.append karr _179_2224))
in (FStar_List.append decls _179_2225)))
end))
in (
# 1825 "FStar.SMTEncoding.Encode.fst"
let aux = (let _179_2229 = (let _179_2228 = (inversion_axioms tapp vars)
in (let _179_2227 = (let _179_2226 = (pretype_axiom tapp vars)
in (_179_2226)::[])
in (FStar_List.append _179_2228 _179_2227)))
in (FStar_List.append kindingAx _179_2229))
in (
# 1830 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _86_2910, _86_2912, _86_2914, _86_2916, _86_2918, _86_2920, _86_2922) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _86_2927, t, _86_2930, n_tps, quals, _86_2934, drange) -> begin
(
# 1838 "FStar.SMTEncoding.Encode.fst"
let _86_2941 = (new_term_constant_and_tok_from_lid env d)
in (match (_86_2941) with
| (ddconstrsym, ddtok, env) -> begin
(
# 1839 "FStar.SMTEncoding.Encode.fst"
let ddtok_tm = (FStar_SMTEncoding_Term.mkApp ((ddtok), ([])))
in (
# 1840 "FStar.SMTEncoding.Encode.fst"
let _86_2945 = (FStar_Syntax_Util.arrow_formals t)
in (match (_86_2945) with
| (formals, t_res) -> begin
(
# 1841 "FStar.SMTEncoding.Encode.fst"
let _86_2948 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_86_2948) with
| (fuel_var, fuel_tm) -> begin
(
# 1842 "FStar.SMTEncoding.Encode.fst"
let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp (("SFuel"), ((fuel_tm)::[])))
in (
# 1843 "FStar.SMTEncoding.Encode.fst"
let _86_2955 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_86_2955) with
| (vars, guards, env', binder_decls, names) -> begin
(
# 1844 "FStar.SMTEncoding.Encode.fst"
let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _179_2231 = (mk_term_projector_name d x)
in ((_179_2231), (FStar_SMTEncoding_Term.Term_sort))))))
in (
# 1845 "FStar.SMTEncoding.Encode.fst"
let datacons = (let _179_2233 = (let _179_2232 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (_179_2232), (true)))
in (FStar_All.pipe_right _179_2233 FStar_SMTEncoding_Term.constructor_to_decl))
in (
# 1846 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply ddtok_tm vars)
in (
# 1847 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1848 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1849 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (
# 1851 "FStar.SMTEncoding.Encode.fst"
let _86_2965 = (encode_term_pred None t env ddtok_tm)
in (match (_86_2965) with
| (tok_typing, decls3) -> begin
(
# 1853 "FStar.SMTEncoding.Encode.fst"
let _86_2972 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_86_2972) with
| (vars', guards', env'', decls_formals, _86_2971) -> begin
(
# 1854 "FStar.SMTEncoding.Encode.fst"
let _86_2977 = (
# 1855 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (
# 1856 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_86_2977) with
| (ty_pred', decls_pred) -> begin
(
# 1858 "FStar.SMTEncoding.Encode.fst"
let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (
# 1859 "FStar.SMTEncoding.Encode.fst"
let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _86_2981 -> begin
(let _179_2235 = (let _179_2234 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) _179_2234))
in (_179_2235)::[])
end)
in (
# 1863 "FStar.SMTEncoding.Encode.fst"
let encode_elim = (fun _86_2984 -> (match (()) with
| () -> begin
(
# 1864 "FStar.SMTEncoding.Encode.fst"
let _86_2987 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_86_2987) with
| (head, args) -> begin
(match ((let _179_2238 = (FStar_Syntax_Subst.compress head)
in _179_2238.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(
# 1868 "FStar.SMTEncoding.Encode.fst"
let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (
# 1869 "FStar.SMTEncoding.Encode.fst"
let _86_3005 = (encode_args args env')
in (match (_86_3005) with
| (encoded_args, arg_decls) -> begin
(
# 1870 "FStar.SMTEncoding.Encode.fst"
let _86_3020 = (FStar_List.fold_left (fun _86_3009 arg -> (match (_86_3009) with
| (env, arg_vars, eqns) -> begin
(
# 1871 "FStar.SMTEncoding.Encode.fst"
let _86_3015 = (let _179_2241 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _179_2241))
in (match (_86_3015) with
| (_86_3012, xv, env) -> begin
(let _179_2243 = (let _179_2242 = (FStar_SMTEncoding_Term.mkEq ((arg), (xv)))
in (_179_2242)::eqns)
in ((env), ((xv)::arg_vars), (_179_2243)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (_86_3020) with
| (_86_3017, arg_vars, eqns) -> begin
(
# 1873 "FStar.SMTEncoding.Encode.fst"
let arg_vars = (FStar_List.rev arg_vars)
in (
# 1874 "FStar.SMTEncoding.Encode.fst"
let ty = (FStar_SMTEncoding_Term.mkApp ((encoded_head), (arg_vars)))
in (
# 1875 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1876 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp ((ddconstrsym), (xvars)))
in (
# 1877 "FStar.SMTEncoding.Encode.fst"
let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (
# 1878 "FStar.SMTEncoding.Encode.fst"
let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (
# 1879 "FStar.SMTEncoding.Encode.fst"
let typing_inversion = (let _179_2250 = (let _179_2249 = (let _179_2248 = (let _179_2247 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _179_2246 = (let _179_2245 = (let _179_2244 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (_179_2244)))
in (FStar_SMTEncoding_Term.mkImp _179_2245))
in ((((ty_pred)::[])::[]), (_179_2247), (_179_2246))))
in (FStar_SMTEncoding_Term.mkForall _179_2248))
in ((_179_2249), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_179_2250))
in (
# 1885 "FStar.SMTEncoding.Encode.fst"
let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(
# 1887 "FStar.SMTEncoding.Encode.fst"
let x = (let _179_2251 = (varops.fresh "x")
in ((_179_2251), (FStar_SMTEncoding_Term.Term_sort)))
in (
# 1888 "FStar.SMTEncoding.Encode.fst"
let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _179_2263 = (let _179_2262 = (let _179_2259 = (let _179_2258 = (let _179_2253 = (let _179_2252 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_179_2252)::[])
in (_179_2253)::[])
in (let _179_2257 = (let _179_2256 = (let _179_2255 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _179_2254 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in ((_179_2255), (_179_2254))))
in (FStar_SMTEncoding_Term.mkImp _179_2256))
in ((_179_2258), ((x)::[]), (_179_2257))))
in (FStar_SMTEncoding_Term.mkForall _179_2259))
in (let _179_2261 = (let _179_2260 = (varops.mk_unique "lextop")
in Some (_179_2260))
in ((_179_2262), (Some ("lextop is top")), (_179_2261))))
in FStar_SMTEncoding_Term.Assume (_179_2263))))
end else begin
(
# 1893 "FStar.SMTEncoding.Encode.fst"
let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _179_2266 = (let _179_2265 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _179_2265 dapp))
in (_179_2266)::[])
end
| _86_3034 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _179_2273 = (let _179_2272 = (let _179_2271 = (let _179_2270 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (let _179_2269 = (let _179_2268 = (let _179_2267 = (FStar_SMTEncoding_Term.mk_and_l prec)
in ((ty_pred), (_179_2267)))
in (FStar_SMTEncoding_Term.mkImp _179_2268))
in ((((ty_pred)::[])::[]), (_179_2270), (_179_2269))))
in (FStar_SMTEncoding_Term.mkForall _179_2271))
in ((_179_2272), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (_179_2273)))
end
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| _86_3038 -> begin
(
# 1903 "FStar.SMTEncoding.Encode.fst"
let _86_3039 = (let _179_2276 = (let _179_2275 = (FStar_Syntax_Print.lid_to_string d)
in (let _179_2274 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _179_2275 _179_2274)))
in (FStar_TypeChecker_Errors.warn drange _179_2276))
in (([]), ([])))
end)
end))
end))
in (
# 1906 "FStar.SMTEncoding.Encode.fst"
let _86_3043 = (encode_elim ())
in (match (_86_3043) with
| (decls2, elim) -> begin
(
# 1907 "FStar.SMTEncoding.Encode.fst"
let g = (let _179_2303 = (let _179_2302 = (let _179_2301 = (let _179_2300 = (let _179_2281 = (let _179_2280 = (let _179_2279 = (let _179_2278 = (let _179_2277 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _179_2277))
in Some (_179_2278))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (_179_2279)))
in FStar_SMTEncoding_Term.DeclFun (_179_2280))
in (_179_2281)::[])
in (let _179_2299 = (let _179_2298 = (let _179_2297 = (let _179_2296 = (let _179_2295 = (let _179_2294 = (let _179_2293 = (let _179_2285 = (let _179_2284 = (let _179_2283 = (let _179_2282 = (FStar_SMTEncoding_Term.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (_179_2282)))
in (FStar_SMTEncoding_Term.mkForall _179_2283))
in ((_179_2284), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_179_2285))
in (let _179_2292 = (let _179_2291 = (let _179_2290 = (let _179_2289 = (let _179_2288 = (let _179_2287 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (let _179_2286 = (FStar_SMTEncoding_Term.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (_179_2287), (_179_2286))))
in (FStar_SMTEncoding_Term.mkForall _179_2288))
in ((_179_2289), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (_179_2290))
in (_179_2291)::[])
in (_179_2293)::_179_2292))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::_179_2294)
in (FStar_List.append _179_2295 elim))
in (FStar_List.append decls_pred _179_2296))
in (FStar_List.append decls_formals _179_2297))
in (FStar_List.append proxy_fresh _179_2298))
in (FStar_List.append _179_2300 _179_2299)))
in (FStar_List.append decls3 _179_2301))
in (FStar_List.append decls2 _179_2302))
in (FStar_List.append binder_decls _179_2303))
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
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _86_3049 se -> (match (_86_3049) with
| (g, env) -> begin
(
# 1926 "FStar.SMTEncoding.Encode.fst"
let _86_3053 = (encode_sigelt env se)
in (match (_86_3053) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))

# 1927 "FStar.SMTEncoding.Encode.fst"
let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (
# 1954 "FStar.SMTEncoding.Encode.fst"
let encode_binding = (fun b _86_3061 -> (match (_86_3061) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_86_3063) -> begin
(((i + 1)), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(
# 1959 "FStar.SMTEncoding.Encode.fst"
let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (
# 1960 "FStar.SMTEncoding.Encode.fst"
let _86_3068 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _179_2318 = (FStar_Syntax_Print.bv_to_string x)
in (let _179_2317 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _179_2316 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _179_2318 _179_2317 _179_2316))))
end else begin
()
end
in (
# 1962 "FStar.SMTEncoding.Encode.fst"
let _86_3072 = (encode_term t1 env)
in (match (_86_3072) with
| (t, decls') -> begin
(
# 1963 "FStar.SMTEncoding.Encode.fst"
let _86_3076 = (let _179_2323 = (let _179_2322 = (let _179_2321 = (FStar_Util.digest_of_string t.FStar_SMTEncoding_Term.hash)
in (let _179_2320 = (let _179_2319 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" _179_2319))
in (Prims.strcat _179_2321 _179_2320)))
in (Prims.strcat "x_" _179_2322))
in (new_term_constant_from_string env x _179_2323))
in (match (_86_3076) with
| (xxsym, xx, env') -> begin
(
# 1966 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (
# 1967 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_Options.log_queries ()) then begin
(let _179_2327 = (let _179_2326 = (FStar_Syntax_Print.bv_to_string x)
in (let _179_2325 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _179_2324 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _179_2326 _179_2325 _179_2324))))
in Some (_179_2327))
end else begin
None
end
in (
# 1971 "FStar.SMTEncoding.Encode.fst"
let ax = (
# 1972 "FStar.SMTEncoding.Encode.fst"
let a_name = Some ((Prims.strcat "binder_" xxsym))
in FStar_SMTEncoding_Term.Assume (((t), (a_name), (a_name))))
in (
# 1974 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun (((xxsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((ax)::[])))
in (((i + 1)), ((FStar_List.append decls g)), (env'))))))
end))
end))))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_86_3084, t)) -> begin
(
# 1980 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env t)
in (
# 1981 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (
# 1983 "FStar.SMTEncoding.Encode.fst"
let _86_3093 = (encode_free_var env fv t t_norm [])
in (match (_86_3093) with
| (g, env') -> begin
(((i + 1)), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(
# 1988 "FStar.SMTEncoding.Encode.fst"
let _86_3107 = (encode_sigelt env se)
in (match (_86_3107) with
| (g, env') -> begin
(((i + 1)), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (
# 1991 "FStar.SMTEncoding.Encode.fst"
let _86_3112 = (FStar_List.fold_right encode_binding bindings ((0), ([]), (env)))
in (match (_86_3112) with
| (_86_3109, decls, env) -> begin
((decls), (env))
end))))

# 1992 "FStar.SMTEncoding.Encode.fst"
let encode_labels = (fun labs -> (
# 1995 "FStar.SMTEncoding.Encode.fst"
let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _86_3119 -> (match (_86_3119) with
| (l, _86_3116, _86_3118) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (
# 1996 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _86_3126 -> (match (_86_3126) with
| (l, _86_3123, _86_3125) -> begin
(let _179_2335 = (FStar_All.pipe_left (fun _179_2331 -> FStar_SMTEncoding_Term.Echo (_179_2331)) (Prims.fst l))
in (let _179_2334 = (let _179_2333 = (let _179_2332 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_179_2332))
in (_179_2333)::[])
in (_179_2335)::_179_2334))
end))))
in ((prefix), (suffix)))))

# 1997 "FStar.SMTEncoding.Encode.fst"
let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 2000 "FStar.SMTEncoding.Encode.fst"
let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _179_2340 = (let _179_2339 = (let _179_2338 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _179_2338; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_179_2339)::[])
in (FStar_ST.op_Colon_Equals last_env _179_2340)))

# 2003 "FStar.SMTEncoding.Encode.fst"
let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| (e)::_86_3132 -> begin
(
# 2006 "FStar.SMTEncoding.Encode.fst"
let _86_3135 = e
in {bindings = _86_3135.bindings; depth = _86_3135.depth; tcenv = tcenv; warn = _86_3135.warn; cache = _86_3135.cache; nolabels = _86_3135.nolabels; use_zfuel_name = _86_3135.use_zfuel_name; encode_non_total_function_typ = _86_3135.encode_non_total_function_typ})
end))

# 2006 "FStar.SMTEncoding.Encode.fst"
let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (_86_3141)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

# 2009 "FStar.SMTEncoding.Encode.fst"
let push_env : Prims.unit  ->  Prims.unit = (fun _86_3143 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| (hd)::tl -> begin
(
# 2013 "FStar.SMTEncoding.Encode.fst"
let refs = (FStar_Util.smap_copy hd.cache)
in (
# 2014 "FStar.SMTEncoding.Encode.fst"
let top = (
# 2014 "FStar.SMTEncoding.Encode.fst"
let _86_3149 = hd
in {bindings = _86_3149.bindings; depth = _86_3149.depth; tcenv = _86_3149.tcenv; warn = _86_3149.warn; cache = refs; nolabels = _86_3149.nolabels; use_zfuel_name = _86_3149.use_zfuel_name; encode_non_total_function_typ = _86_3149.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

# 2015 "FStar.SMTEncoding.Encode.fst"
let pop_env : Prims.unit  ->  Prims.unit = (fun _86_3152 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| (_86_3156)::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

# 2018 "FStar.SMTEncoding.Encode.fst"
let mark_env : Prims.unit  ->  Prims.unit = (fun _86_3158 -> (match (()) with
| () -> begin
(push_env ())
end))

# 2019 "FStar.SMTEncoding.Encode.fst"
let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _86_3159 -> (match (()) with
| () -> begin
(pop_env ())
end))

# 2020 "FStar.SMTEncoding.Encode.fst"
let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _86_3160 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| (hd)::(_86_3163)::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _86_3168 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 2024 "FStar.SMTEncoding.Encode.fst"
let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (
# 2028 "FStar.SMTEncoding.Encode.fst"
let _86_3170 = (init_env tcenv)
in (
# 2029 "FStar.SMTEncoding.Encode.fst"
let _86_3172 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))

# 2030 "FStar.SMTEncoding.Encode.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 2032 "FStar.SMTEncoding.Encode.fst"
let _86_3175 = (push_env ())
in (
# 2033 "FStar.SMTEncoding.Encode.fst"
let _86_3177 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))

# 2034 "FStar.SMTEncoding.Encode.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 2036 "FStar.SMTEncoding.Encode.fst"
let _86_3180 = (let _179_2361 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _179_2361))
in (
# 2037 "FStar.SMTEncoding.Encode.fst"
let _86_3182 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))

# 2038 "FStar.SMTEncoding.Encode.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 2040 "FStar.SMTEncoding.Encode.fst"
let _86_3185 = (mark_env ())
in (
# 2041 "FStar.SMTEncoding.Encode.fst"
let _86_3187 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))

# 2042 "FStar.SMTEncoding.Encode.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 2044 "FStar.SMTEncoding.Encode.fst"
let _86_3190 = (reset_mark_env ())
in (
# 2045 "FStar.SMTEncoding.Encode.fst"
let _86_3192 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))

# 2046 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun msg -> (
# 2048 "FStar.SMTEncoding.Encode.fst"
let _86_3195 = (commit_mark_env ())
in (
# 2049 "FStar.SMTEncoding.Encode.fst"
let _86_3197 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))

# 2050 "FStar.SMTEncoding.Encode.fst"
let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (
# 2052 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(let _179_2377 = (let _179_2376 = (let _179_2375 = (let _179_2374 = (let _179_2373 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _179_2373 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _179_2374 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _179_2375))
in FStar_SMTEncoding_Term.Caption (_179_2376))
in (_179_2377)::decls)
end else begin
decls
end)
in (
# 2056 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 2057 "FStar.SMTEncoding.Encode.fst"
let _86_3206 = (encode_sigelt env se)
in (match (_86_3206) with
| (decls, env) -> begin
(
# 2058 "FStar.SMTEncoding.Encode.fst"
let _86_3207 = (set_env env)
in (let _179_2378 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _179_2378)))
end)))))

# 2059 "FStar.SMTEncoding.Encode.fst"
let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (
# 2062 "FStar.SMTEncoding.Encode.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 2063 "FStar.SMTEncoding.Encode.fst"
let _86_3212 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _179_2383 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _179_2383))
end else begin
()
end
in (
# 2065 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 2066 "FStar.SMTEncoding.Encode.fst"
let _86_3219 = (encode_signature (
# 2066 "FStar.SMTEncoding.Encode.fst"
let _86_3215 = env
in {bindings = _86_3215.bindings; depth = _86_3215.depth; tcenv = _86_3215.tcenv; warn = false; cache = _86_3215.cache; nolabels = _86_3215.nolabels; use_zfuel_name = _86_3215.use_zfuel_name; encode_non_total_function_typ = _86_3215.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_86_3219) with
| (decls, env) -> begin
(
# 2067 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_Options.log_queries ()) then begin
(
# 2069 "FStar.SMTEncoding.Encode.fst"
let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (
# 2072 "FStar.SMTEncoding.Encode.fst"
let _86_3225 = (set_env (
# 2072 "FStar.SMTEncoding.Encode.fst"
let _86_3223 = env
in {bindings = _86_3223.bindings; depth = _86_3223.depth; tcenv = _86_3223.tcenv; warn = true; cache = _86_3223.cache; nolabels = _86_3223.nolabels; use_zfuel_name = _86_3223.use_zfuel_name; encode_non_total_function_typ = _86_3223.encode_non_total_function_typ}))
in (
# 2073 "FStar.SMTEncoding.Encode.fst"
let _86_3227 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (
# 2074 "FStar.SMTEncoding.Encode.fst"
let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))

# 2077 "FStar.SMTEncoding.Encode.fst"
let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> (
# 2083 "FStar.SMTEncoding.Encode.fst"
let _86_3233 = (let _179_2401 = (let _179_2400 = (FStar_TypeChecker_Env.current_module tcenv)
in _179_2400.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name _179_2401))
in (
# 2084 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 2085 "FStar.SMTEncoding.Encode.fst"
let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (
# 2086 "FStar.SMTEncoding.Encode.fst"
let _86_3258 = (
# 2087 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(
# 2089 "FStar.SMTEncoding.Encode.fst"
let _86_3247 = (aux rest)
in (match (_86_3247) with
| (out, rest) -> begin
(
# 2090 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _179_2407 = (let _179_2406 = (FStar_Syntax_Syntax.mk_binder (
# 2091 "FStar.SMTEncoding.Encode.fst"
let _86_3249 = x
in {FStar_Syntax_Syntax.ppname = _86_3249.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _86_3249.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_179_2406)::out)
in ((_179_2407), (rest))))
end))
end
| _86_3252 -> begin
(([]), (bindings))
end))
in (
# 2093 "FStar.SMTEncoding.Encode.fst"
let _86_3255 = (aux bindings)
in (match (_86_3255) with
| (closing, bindings) -> begin
(let _179_2408 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((_179_2408), (bindings)))
end)))
in (match (_86_3258) with
| (q, bindings) -> begin
(
# 2096 "FStar.SMTEncoding.Encode.fst"
let _86_3267 = (let _179_2410 = (FStar_List.filter (fun _86_24 -> (match (_86_24) with
| FStar_TypeChecker_Env.Binding_sig (_86_3261) -> begin
false
end
| _86_3264 -> begin
true
end)) bindings)
in (encode_env_bindings env _179_2410))
in (match (_86_3267) with
| (env_decls, env) -> begin
(
# 2097 "FStar.SMTEncoding.Encode.fst"
let _86_3268 = if (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery")))) then begin
(let _179_2411 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _179_2411))
end else begin
()
end
in (
# 2101 "FStar.SMTEncoding.Encode.fst"
let _86_3272 = (encode_formula q env)
in (match (_86_3272) with
| (phi, qdecls) -> begin
(
# 2102 "FStar.SMTEncoding.Encode.fst"
let _86_3277 = (let _179_2412 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _179_2412 phi))
in (match (_86_3277) with
| (phi, labels, _86_3276) -> begin
(
# 2103 "FStar.SMTEncoding.Encode.fst"
let _86_3280 = (encode_labels labels)
in (match (_86_3280) with
| (label_prefix, label_suffix) -> begin
(
# 2104 "FStar.SMTEncoding.Encode.fst"
let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (
# 2108 "FStar.SMTEncoding.Encode.fst"
let qry = (let _179_2416 = (let _179_2415 = (FStar_SMTEncoding_Term.mkNot phi)
in (let _179_2414 = (let _179_2413 = (varops.mk_unique "@query")
in Some (_179_2413))
in ((_179_2415), (Some ("query")), (_179_2414))))
in FStar_SMTEncoding_Term.Assume (_179_2416))
in (
# 2109 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end))
end)))
end))
end))))))

# 2110 "FStar.SMTEncoding.Encode.fst"
let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (
# 2113 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 2114 "FStar.SMTEncoding.Encode.fst"
let _86_3287 = (push "query")
in (
# 2115 "FStar.SMTEncoding.Encode.fst"
let _86_3292 = (encode_formula q env)
in (match (_86_3292) with
| (f, _86_3291) -> begin
(
# 2116 "FStar.SMTEncoding.Encode.fst"
let _86_3293 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _86_3297) -> begin
true
end
| _86_3301 -> begin
false
end))
end)))))





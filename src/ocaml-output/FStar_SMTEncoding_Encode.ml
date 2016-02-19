
open Prims
# 34 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun x tl -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
tl
end else begin
(x)::tl
end)

# 35 "FStar.SMTEncoding.Encode.fst"
let withenv = (fun c _77_28 -> (match (_77_28) with
| (a, b) -> begin
(a, b, c)
end))

# 36 "FStar.SMTEncoding.Encode.fst"
let vargs = (fun args -> (FStar_List.filter (fun _77_1 -> (match (_77_1) with
| (FStar_Util.Inl (_77_32), _77_35) -> begin
false
end
| _77_38 -> begin
true
end)) args))

# 37 "FStar.SMTEncoding.Encode.fst"
let subst_lcomp_opt : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (l) -> begin
(let _156_13 = (let _156_12 = (let _156_11 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _156_11))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _156_12))
in Some (_156_13))
end))

# 42 "FStar.SMTEncoding.Encode.fst"
let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))

# 43 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (
# 44 "FStar.SMTEncoding.Encode.fst"
let a = (
# 44 "FStar.SMTEncoding.Encode.fst"
let _77_47 = a
in (let _156_20 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _156_20; FStar_Syntax_Syntax.index = _77_47.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _77_47.FStar_Syntax_Syntax.sort}))
in (let _156_21 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _156_21))))

# 46 "FStar.SMTEncoding.Encode.fst"
let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (
# 47 "FStar.SMTEncoding.Encode.fst"
let fail = (fun _77_54 -> (match (()) with
| () -> begin
(let _156_31 = (let _156_30 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _156_30 lid.FStar_Ident.str))
in (FStar_All.failwith _156_31))
end))
in (
# 48 "FStar.SMTEncoding.Encode.fst"
let _77_58 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_77_58) with
| (_77_56, t) -> begin
(match ((let _156_32 = (FStar_Syntax_Subst.compress t)
in _156_32.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 51 "FStar.SMTEncoding.Encode.fst"
let _77_66 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_77_66) with
| (binders, _77_65) -> begin
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
| _77_69 -> begin
(fail ())
end)
end))))

# 57 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _156_38 = (let _156_37 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _156_37))
in (FStar_All.pipe_left escape _156_38)))

# 58 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _156_44 = (let _156_43 = (mk_term_projector_name lid a)
in (_156_43, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _156_44)))

# 60 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _156_50 = (let _156_49 = (mk_term_projector_name_by_pos lid i)
in (_156_49, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _156_50)))

# 62 "FStar.SMTEncoding.Encode.fst"
let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

# 65 "FStar.SMTEncoding.Encode.fst"
type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int}

# 65 "FStar.SMTEncoding.Encode.fst"
let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))

# 77 "FStar.SMTEncoding.Encode.fst"
let varops : varops_t = (
# 78 "FStar.SMTEncoding.Encode.fst"
let initial_ctr = 10
in (
# 79 "FStar.SMTEncoding.Encode.fst"
let ctr = (FStar_Util.mk_ref initial_ctr)
in (
# 80 "FStar.SMTEncoding.Encode.fst"
let new_scope = (fun _77_93 -> (match (()) with
| () -> begin
(let _156_154 = (FStar_Util.smap_create 100)
in (let _156_153 = (FStar_Util.smap_create 100)
in (_156_154, _156_153)))
end))
in (
# 81 "FStar.SMTEncoding.Encode.fst"
let scopes = (let _156_156 = (let _156_155 = (new_scope ())
in (_156_155)::[])
in (FStar_Util.mk_ref _156_156))
in (
# 82 "FStar.SMTEncoding.Encode.fst"
let mk_unique = (fun y -> (
# 83 "FStar.SMTEncoding.Encode.fst"
let y = (escape y)
in (
# 84 "FStar.SMTEncoding.Encode.fst"
let y = (match ((let _156_160 = (FStar_ST.read scopes)
in (FStar_Util.find_map _156_160 (fun _77_101 -> (match (_77_101) with
| (names, _77_100) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_77_104) -> begin
(
# 86 "FStar.SMTEncoding.Encode.fst"
let _77_106 = (FStar_Util.incr ctr)
in (let _156_162 = (let _156_161 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _156_161))
in (Prims.strcat (Prims.strcat y "__") _156_162)))
end)
in (
# 87 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _156_164 = (let _156_163 = (FStar_ST.read scopes)
in (FStar_List.hd _156_163))
in (FStar_All.pipe_left Prims.fst _156_164))
in (
# 88 "FStar.SMTEncoding.Encode.fst"
let _77_110 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (
# 89 "FStar.SMTEncoding.Encode.fst"
let new_var = (fun pp rn -> (let _156_171 = (let _156_169 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _156_169 "__"))
in (let _156_170 = (FStar_Util.string_of_int rn)
in (Prims.strcat _156_171 _156_170))))
in (
# 90 "FStar.SMTEncoding.Encode.fst"
let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (
# 91 "FStar.SMTEncoding.Encode.fst"
let next_id = (fun _77_118 -> (match (()) with
| () -> begin
(
# 91 "FStar.SMTEncoding.Encode.fst"
let _77_119 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (
# 92 "FStar.SMTEncoding.Encode.fst"
let fresh = (fun pfx -> (let _156_179 = (let _156_178 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _156_178))
in (FStar_Util.format2 "%s_%s" pfx _156_179)))
in (
# 93 "FStar.SMTEncoding.Encode.fst"
let string_const = (fun s -> (match ((let _156_183 = (FStar_ST.read scopes)
in (FStar_Util.find_map _156_183 (fun _77_128 -> (match (_77_128) with
| (_77_126, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(
# 96 "FStar.SMTEncoding.Encode.fst"
let id = (next_id ())
in (
# 97 "FStar.SMTEncoding.Encode.fst"
let f = (let _156_184 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _156_184))
in (
# 98 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _156_186 = (let _156_185 = (FStar_ST.read scopes)
in (FStar_List.hd _156_185))
in (FStar_All.pipe_left Prims.snd _156_186))
in (
# 99 "FStar.SMTEncoding.Encode.fst"
let _77_135 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (
# 101 "FStar.SMTEncoding.Encode.fst"
let push = (fun _77_138 -> (match (()) with
| () -> begin
(let _156_191 = (let _156_190 = (new_scope ())
in (let _156_189 = (FStar_ST.read scopes)
in (_156_190)::_156_189))
in (FStar_ST.op_Colon_Equals scopes _156_191))
end))
in (
# 102 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _77_140 -> (match (()) with
| () -> begin
(let _156_195 = (let _156_194 = (FStar_ST.read scopes)
in (FStar_List.tl _156_194))
in (FStar_ST.op_Colon_Equals scopes _156_195))
end))
in (
# 103 "FStar.SMTEncoding.Encode.fst"
let mark = (fun _77_142 -> (match (()) with
| () -> begin
(push ())
end))
in (
# 104 "FStar.SMTEncoding.Encode.fst"
let reset_mark = (fun _77_144 -> (match (()) with
| () -> begin
(pop ())
end))
in (
# 105 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun _77_146 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(
# 107 "FStar.SMTEncoding.Encode.fst"
let _77_159 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (
# 108 "FStar.SMTEncoding.Encode.fst"
let _77_164 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _77_167 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

# 122 "FStar.SMTEncoding.Encode.fst"
let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (
# 122 "FStar.SMTEncoding.Encode.fst"
let _77_169 = x
in (let _156_210 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _156_210; FStar_Syntax_Syntax.index = _77_169.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _77_169.FStar_Syntax_Syntax.sort})))

# 126 "FStar.SMTEncoding.Encode.fst"
type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option)

# 127 "FStar.SMTEncoding.Encode.fst"
let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

# 128 "FStar.SMTEncoding.Encode.fst"
let is_Binding_fvar = (fun _discr_ -> (match (_discr_) with
| Binding_fvar (_) -> begin
true
end
| _ -> begin
false
end))

# 127 "FStar.SMTEncoding.Encode.fst"
let ___Binding_var____0 : binding  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) = (fun projectee -> (match (projectee) with
| Binding_var (_77_173) -> begin
_77_173
end))

# 128 "FStar.SMTEncoding.Encode.fst"
let ___Binding_fvar____0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_77_176) -> begin
_77_176
end))

# 131 "FStar.SMTEncoding.Encode.fst"
let binder_of_eithervar = (fun v -> (v, None))

# 132 "FStar.SMTEncoding.Encode.fst"
type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

# 132 "FStar.SMTEncoding.Encode.fst"
let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))

# 142 "FStar.SMTEncoding.Encode.fst"
let print_env : env_t  ->  Prims.string = (fun e -> (let _156_268 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _77_2 -> (match (_77_2) with
| Binding_var (x, _77_191) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _77_196, _77_198, _77_200) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _156_268 (FStar_String.concat ", "))))

# 147 "FStar.SMTEncoding.Encode.fst"
let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

# 149 "FStar.SMTEncoding.Encode.fst"
let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _156_278 = (FStar_Syntax_Print.term_to_string t)
in Some (_156_278))
end else begin
None
end)

# 154 "FStar.SMTEncoding.Encode.fst"
let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (
# 154 "FStar.SMTEncoding.Encode.fst"
let xsym = (varops.fresh x)
in (let _156_283 = (FStar_SMTEncoding_Term.mkFreeV (xsym, s))
in (xsym, _156_283))))

# 158 "FStar.SMTEncoding.Encode.fst"
let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 159 "FStar.SMTEncoding.Encode.fst"
let ysym = (let _156_288 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _156_288))
in (
# 160 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV (ysym, FStar_SMTEncoding_Term.Term_sort))
in (ysym, y, (
# 161 "FStar.SMTEncoding.Encode.fst"
let _77_214 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _77_214.tcenv; warn = _77_214.warn; cache = _77_214.cache; nolabels = _77_214.nolabels; use_zfuel_name = _77_214.use_zfuel_name; encode_non_total_function_typ = _77_214.encode_non_total_function_typ})))))

# 162 "FStar.SMTEncoding.Encode.fst"
let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 163 "FStar.SMTEncoding.Encode.fst"
let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (
# 164 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkApp (ysym, []))
in (ysym, y, (
# 165 "FStar.SMTEncoding.Encode.fst"
let _77_220 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _77_220.depth; tcenv = _77_220.tcenv; warn = _77_220.warn; cache = _77_220.cache; nolabels = _77_220.nolabels; use_zfuel_name = _77_220.use_zfuel_name; encode_non_total_function_typ = _77_220.encode_non_total_function_typ})))))

# 166 "FStar.SMTEncoding.Encode.fst"
let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (
# 167 "FStar.SMTEncoding.Encode.fst"
let _77_225 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _77_225.depth; tcenv = _77_225.tcenv; warn = _77_225.warn; cache = _77_225.cache; nolabels = _77_225.nolabels; use_zfuel_name = _77_225.use_zfuel_name; encode_non_total_function_typ = _77_225.encode_non_total_function_typ}))

# 168 "FStar.SMTEncoding.Encode.fst"
let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (match ((lookup_binding env (fun _77_3 -> (match (_77_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a) -> begin
Some ((b, t))
end
| _77_235 -> begin
None
end)))) with
| None -> begin
(let _156_305 = (let _156_304 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found: %s" _156_304))
in (FStar_All.failwith _156_305))
end
| Some (b, t) -> begin
t
end))

# 174 "FStar.SMTEncoding.Encode.fst"
let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (
# 175 "FStar.SMTEncoding.Encode.fst"
let fname = (varops.new_fvar x)
in (
# 176 "FStar.SMTEncoding.Encode.fst"
let ftok = (Prims.strcat fname "@tok")
in (let _156_316 = (
# 178 "FStar.SMTEncoding.Encode.fst"
let _77_245 = env
in (let _156_315 = (let _156_314 = (let _156_313 = (let _156_312 = (let _156_311 = (FStar_SMTEncoding_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _156_310 -> Some (_156_310)) _156_311))
in (x, fname, _156_312, None))
in Binding_fvar (_156_313))
in (_156_314)::env.bindings)
in {bindings = _156_315; depth = _77_245.depth; tcenv = _77_245.tcenv; warn = _77_245.warn; cache = _77_245.cache; nolabels = _77_245.nolabels; use_zfuel_name = _77_245.use_zfuel_name; encode_non_total_function_typ = _77_245.encode_non_total_function_typ}))
in (fname, ftok, _156_316)))))

# 179 "FStar.SMTEncoding.Encode.fst"
let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _77_4 -> (match (_77_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _77_257 -> begin
None
end))))

# 181 "FStar.SMTEncoding.Encode.fst"
let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _156_327 = (let _156_326 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _156_326))
in (FStar_All.failwith _156_327))
end
| Some (s) -> begin
s
end))

# 185 "FStar.SMTEncoding.Encode.fst"
let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (
# 186 "FStar.SMTEncoding.Encode.fst"
let _77_267 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _77_267.depth; tcenv = _77_267.tcenv; warn = _77_267.warn; cache = _77_267.cache; nolabels = _77_267.nolabels; use_zfuel_name = _77_267.use_zfuel_name; encode_non_total_function_typ = _77_267.encode_non_total_function_typ}))

# 187 "FStar.SMTEncoding.Encode.fst"
let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (
# 188 "FStar.SMTEncoding.Encode.fst"
let _77_276 = (lookup_lid env x)
in (match (_77_276) with
| (t1, t2, _77_275) -> begin
(
# 189 "FStar.SMTEncoding.Encode.fst"
let t3 = (let _156_344 = (let _156_343 = (let _156_342 = (FStar_SMTEncoding_Term.mkApp ("ZFuel", []))
in (_156_342)::[])
in (f, _156_343))
in (FStar_SMTEncoding_Term.mkApp _156_344))
in (
# 190 "FStar.SMTEncoding.Encode.fst"
let _77_278 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _77_278.depth; tcenv = _77_278.tcenv; warn = _77_278.warn; cache = _77_278.cache; nolabels = _77_278.nolabels; use_zfuel_name = _77_278.use_zfuel_name; encode_non_total_function_typ = _77_278.encode_non_total_function_typ}))
end)))

# 191 "FStar.SMTEncoding.Encode.fst"
let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env l -> (match ((try_lookup_lid env l)) with
| None -> begin
None
end
| Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
Some (f)
end
| _77_291 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_77_295, fuel::[]) -> begin
if (let _156_350 = (let _156_349 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _156_349 Prims.fst))
in (FStar_Util.starts_with _156_350 "fuel")) then begin
(let _156_353 = (let _156_352 = (FStar_SMTEncoding_Term.mkFreeV (name, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_ApplyTF _156_352 fuel))
in (FStar_All.pipe_left (fun _156_351 -> Some (_156_351)) _156_353))
end else begin
Some (t)
end
end
| _77_301 -> begin
Some (t)
end)
end
| _77_303 -> begin
None
end)
end)
end))

# 208 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var = (fun env a -> (match ((try_lookup_free_var env a.FStar_Syntax_Syntax.v)) with
| Some (t) -> begin
t
end
| None -> begin
(let _156_357 = (let _156_356 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _156_356))
in (FStar_All.failwith _156_357))
end))

# 212 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_name = (fun env a -> (
# 212 "FStar.SMTEncoding.Encode.fst"
let _77_316 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_77_316) with
| (x, _77_313, _77_315) -> begin
x
end)))

# 213 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_sym = (fun env a -> (
# 214 "FStar.SMTEncoding.Encode.fst"
let _77_322 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_77_322) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _77_326; FStar_SMTEncoding_Term.freevars = _77_324}) when env.use_zfuel_name -> begin
(g, zf)
end
| _77_334 -> begin
(match (sym) with
| None -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _77_344 -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end)
end)
end)
end)))

# 225 "FStar.SMTEncoding.Encode.fst"
let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _77_5 -> (match (_77_5) with
| Binding_fvar (_77_349, nm', tok, _77_353) when (nm = nm') -> begin
tok
end
| _77_357 -> begin
None
end))))

# 234 "FStar.SMTEncoding.Encode.fst"
let mkForall_fuel' = (fun n _77_362 -> (match (_77_362) with
| (pats, vars, body) -> begin
(
# 235 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _77_364 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(
# 238 "FStar.SMTEncoding.Encode.fst"
let _77_367 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_77_367) with
| (fsym, fterm) -> begin
(
# 239 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _77_377 -> begin
p
end)))))
in (
# 243 "FStar.SMTEncoding.Encode.fst"
let pats = (FStar_List.map add_fuel pats)
in (
# 244 "FStar.SMTEncoding.Encode.fst"
let body = (match (body.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, guard::body'::[]) -> begin
(
# 246 "FStar.SMTEncoding.Encode.fst"
let guard = (match (guard.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, guards) -> begin
(let _156_374 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _156_374))
end
| _77_390 -> begin
(let _156_375 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _156_375 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp (guard, body')))
end
| _77_393 -> begin
body
end)
in (
# 251 "FStar.SMTEncoding.Encode.fst"
let vars = ((fsym, FStar_SMTEncoding_Term.Fuel_sort))::vars
in (FStar_SMTEncoding_Term.mkForall (pats, vars, body))))))
end))
end)
end))

# 254 "FStar.SMTEncoding.Encode.fst"
let mkForall_fuel : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' 1)

# 256 "FStar.SMTEncoding.Encode.fst"
let head_normal : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (
# 257 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_fvar (v, _)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (v, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _156_381 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv v.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _156_381 FStar_Option.isNone))
end
| _77_438 -> begin
false
end)))

# 269 "FStar.SMTEncoding.Encode.fst"
let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)

# 272 "FStar.SMTEncoding.Encode.fst"
let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))

# 274 "FStar.SMTEncoding.Encode.fst"
let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _156_394 = (let _156_392 = (FStar_Syntax_Syntax.null_binder t)
in (_156_392)::[])
in (let _156_393 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.true_lid FStar_Range.dummyRange)
in (FStar_Syntax_Util.abs _156_394 _156_393 None))))

# 279 "FStar.SMTEncoding.Encode.fst"
let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _156_401 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _156_401))
end
| s -> begin
(
# 282 "FStar.SMTEncoding.Encode.fst"
let _77_450 = ()
in (let _156_402 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _156_402)))
end)) e)))

# 283 "FStar.SMTEncoding.Encode.fst"
let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))

# 285 "FStar.SMTEncoding.Encode.fst"
let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _77_6 -> (match (_77_6) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _77_460 -> begin
false
end))

# 290 "FStar.SMTEncoding.Encode.fst"
let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (
# 291 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun t xs -> (match ((t.FStar_SMTEncoding_Term.tm, xs)) with
| (FStar_SMTEncoding_Term.App (app, f::{FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _77_471; FStar_SMTEncoding_Term.freevars = _77_469}::[]), x::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _77_489) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _77_496 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_77_498, []) -> begin
(
# 302 "FStar.SMTEncoding.Encode.fst"
let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _77_504 -> begin
None
end))
in (aux t (FStar_List.rev vars))))

# 333 "FStar.SMTEncoding.Encode.fst"
type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)

# 334 "FStar.SMTEncoding.Encode.fst"
type labels =
label Prims.list

# 335 "FStar.SMTEncoding.Encode.fst"
type pattern =
{pat_vars : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t); guard : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term; projections : FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list}

# 335 "FStar.SMTEncoding.Encode.fst"
let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))

# 341 "FStar.SMTEncoding.Encode.fst"
exception Let_rec_unencodeable

# 341 "FStar.SMTEncoding.Encode.fst"
let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable (_) -> begin
true
end
| _ -> begin
false
end))

# 343 "FStar.SMTEncoding.Encode.fst"
let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _77_7 -> (match (_77_7) with
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
(let _156_456 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _156_456))
end
| FStar_Const.Const_uint8 (i) -> begin
(let _156_457 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_SMTEncoding_Term.boxInt _156_457))
end
| FStar_Const.Const_int (i) -> begin
(let _156_458 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _156_458))
end
| FStar_Const.Const_int32 (i) -> begin
(let _156_462 = (let _156_461 = (let _156_460 = (let _156_459 = (FStar_SMTEncoding_Term.mkInteger32 i)
in (FStar_SMTEncoding_Term.boxInt _156_459))
in (_156_460)::[])
in ("FStar.Int32.Int32", _156_461))
in (FStar_SMTEncoding_Term.mkApp _156_462))
end
| FStar_Const.Const_string (bytes, _77_526) -> begin
(let _156_463 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _156_463))
end
| c -> begin
(let _156_465 = (let _156_464 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _156_464))
in (FStar_All.failwith _156_465))
end))

# 354 "FStar.SMTEncoding.Encode.fst"
let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (
# 355 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t -> (
# 356 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_77_537) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_77_540) -> begin
(let _156_474 = (FStar_Syntax_Util.unrefine t)
in (aux true _156_474))
end
| _77_543 -> begin
if norm then begin
(let _156_475 = (whnf env t)
in (aux false _156_475))
end else begin
(let _156_478 = (let _156_477 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _156_476 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _156_477 _156_476)))
in (FStar_All.failwith _156_478))
end
end)))
in (aux true t0)))

# 365 "FStar.SMTEncoding.Encode.fst"
let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (
# 366 "FStar.SMTEncoding.Encode.fst"
let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _77_551 -> begin
(let _156_481 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _156_481))
end)))

# 372 "FStar.SMTEncoding.Encode.fst"
let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (
# 379 "FStar.SMTEncoding.Encode.fst"
let _77_555 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _156_531 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _156_531))
end else begin
()
end
in (
# 381 "FStar.SMTEncoding.Encode.fst"
let _77_583 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _77_562 b -> (match (_77_562) with
| (vars, guards, env, decls, names) -> begin
(
# 382 "FStar.SMTEncoding.Encode.fst"
let _77_577 = (
# 383 "FStar.SMTEncoding.Encode.fst"
let x = (unmangle (Prims.fst b))
in (
# 384 "FStar.SMTEncoding.Encode.fst"
let _77_568 = (gen_term_var env x)
in (match (_77_568) with
| (xxsym, xx, env') -> begin
(
# 385 "FStar.SMTEncoding.Encode.fst"
let _77_571 = (let _156_534 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _156_534 env xx))
in (match (_77_571) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_SMTEncoding_Term.Term_sort), guard_x_t, env', decls', x)
end))
end)))
in (match (_77_577) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_77_583) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 400 "FStar.SMTEncoding.Encode.fst"
let _77_590 = (encode_term t env)
in (match (_77_590) with
| (t, decls) -> begin
(let _156_539 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_156_539, decls))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 404 "FStar.SMTEncoding.Encode.fst"
let _77_597 = (encode_term t env)
in (match (_77_597) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _156_544 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in (_156_544, decls))
end
| Some (f) -> begin
(let _156_545 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in (_156_545, decls))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (
# 412 "FStar.SMTEncoding.Encode.fst"
let t0 = (FStar_Syntax_Subst.compress t)
in (
# 413 "FStar.SMTEncoding.Encode.fst"
let _77_604 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _156_550 = (FStar_Syntax_Print.tag_of_term t)
in (let _156_549 = (FStar_Syntax_Print.tag_of_term t0)
in (let _156_548 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _156_550 _156_549 _156_548))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _156_555 = (let _156_554 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _156_553 = (FStar_Syntax_Print.tag_of_term t0)
in (let _156_552 = (FStar_Syntax_Print.term_to_string t0)
in (let _156_551 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _156_554 _156_553 _156_552 _156_551)))))
in (FStar_All.failwith _156_555))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _156_557 = (let _156_556 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _156_556))
in (FStar_All.failwith _156_557))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _77_615) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _77_620) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 429 "FStar.SMTEncoding.Encode.fst"
let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Syntax_Syntax.Tm_fvar (v, _77_628) -> begin
(let _156_558 = (lookup_free_var env v)
in (_156_558, []))
end
| FStar_Syntax_Syntax.Tm_type (_77_632) -> begin
(FStar_SMTEncoding_Term.mk_Term_type, [])
end
| FStar_Syntax_Syntax.Tm_uinst (t, _77_636) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _156_559 = (encode_const c)
in (_156_559, []))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 445 "FStar.SMTEncoding.Encode.fst"
let _77_647 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_77_647) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(
# 449 "FStar.SMTEncoding.Encode.fst"
let _77_654 = (encode_binders None binders env)
in (match (_77_654) with
| (vars, guards, env', decls, _77_653) -> begin
(
# 450 "FStar.SMTEncoding.Encode.fst"
let fsym = (let _156_560 = (varops.fresh "f")
in (_156_560, FStar_SMTEncoding_Term.Term_sort))
in (
# 451 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 452 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 453 "FStar.SMTEncoding.Encode.fst"
let _77_660 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_77_660) with
| (pre_opt, res_t) -> begin
(
# 454 "FStar.SMTEncoding.Encode.fst"
let _77_663 = (encode_term_pred None res_t env' app)
in (match (_77_663) with
| (res_pred, decls') -> begin
(
# 455 "FStar.SMTEncoding.Encode.fst"
let _77_672 = (match (pre_opt) with
| None -> begin
(let _156_561 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_156_561, decls))
end
| Some (pre) -> begin
(
# 458 "FStar.SMTEncoding.Encode.fst"
let _77_669 = (encode_formula pre env')
in (match (_77_669) with
| (guard, decls0) -> begin
(let _156_562 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in (_156_562, (FStar_List.append decls decls0)))
end))
end)
in (match (_77_672) with
| (guards, guard_decls) -> begin
(
# 460 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _156_564 = (let _156_563 = (FStar_SMTEncoding_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _156_563))
in (FStar_SMTEncoding_Term.mkForall _156_564))
in (
# 465 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _156_566 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _156_566 (FStar_List.filter (fun _77_677 -> (match (_77_677) with
| (x, _77_676) -> begin
(x <> (Prims.fst fsym))
end)))))
in (
# 466 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _77_683) -> begin
(let _156_569 = (let _156_568 = (let _156_567 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t', _156_567))
in (FStar_SMTEncoding_Term.mkApp _156_568))
in (_156_569, []))
end
| None -> begin
(
# 472 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Tm_arrow")
in (
# 473 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 474 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _156_570 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_156_570))
end else begin
None
end
in (
# 479 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, caption))
in (
# 481 "FStar.SMTEncoding.Encode.fst"
let t = (let _156_572 = (let _156_571 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _156_571))
in (FStar_SMTEncoding_Term.mkApp _156_572))
in (
# 482 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 484 "FStar.SMTEncoding.Encode.fst"
let k_assumption = (let _156_574 = (let _156_573 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_156_573, Some ((Prims.strcat tsym " kinding"))))
in FStar_SMTEncoding_Term.Assume (_156_574))
in (
# 486 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 487 "FStar.SMTEncoding.Encode.fst"
let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (
# 488 "FStar.SMTEncoding.Encode.fst"
let pre_typing = (let _156_581 = (let _156_580 = (let _156_579 = (let _156_578 = (let _156_577 = (let _156_576 = (let _156_575 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _156_575))
in (f_has_t, _156_576))
in (FStar_SMTEncoding_Term.mkImp _156_577))
in (((f_has_t)::[])::[], (fsym)::cvars, _156_578))
in (mkForall_fuel _156_579))
in (_156_580, Some ("pre-typing for functions")))
in FStar_SMTEncoding_Term.Assume (_156_581))
in (
# 489 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _156_585 = (let _156_584 = (let _156_583 = (let _156_582 = (FStar_SMTEncoding_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _156_582))
in (FStar_SMTEncoding_Term.mkForall _156_583))
in (_156_584, Some ((Prims.strcat tsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_156_585))
in (
# 492 "FStar.SMTEncoding.Encode.fst"
let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (
# 493 "FStar.SMTEncoding.Encode.fst"
let _77_699 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(
# 497 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Non_total_Tm_arrow")
in (
# 498 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, [], FStar_SMTEncoding_Term.Term_sort, None))
in (
# 499 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_SMTEncoding_Term.mkApp (tsym, []))
in (
# 500 "FStar.SMTEncoding.Encode.fst"
let t_kinding = (let _156_587 = (let _156_586 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (_156_586, None))
in FStar_SMTEncoding_Term.Assume (_156_587))
in (
# 501 "FStar.SMTEncoding.Encode.fst"
let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)
in (
# 502 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 503 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 504 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _156_594 = (let _156_593 = (let _156_592 = (let _156_591 = (let _156_590 = (let _156_589 = (let _156_588 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _156_588))
in (f_has_t, _156_589))
in (FStar_SMTEncoding_Term.mkImp _156_590))
in (((f_has_t)::[])::[], (fsym)::[], _156_591))
in (mkForall_fuel _156_592))
in (_156_593, Some ("pre-typing")))
in FStar_SMTEncoding_Term.Assume (_156_594))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_77_710) -> begin
(
# 511 "FStar.SMTEncoding.Encode.fst"
let _77_730 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _77_717; FStar_Syntax_Syntax.pos = _77_715; FStar_Syntax_Syntax.vars = _77_713} -> begin
(
# 513 "FStar.SMTEncoding.Encode.fst"
let _77_725 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_77_725) with
| (b, f) -> begin
(let _156_596 = (let _156_595 = (FStar_List.hd b)
in (Prims.fst _156_595))
in (_156_596, f))
end))
end
| _77_727 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_77_730) with
| (x, f) -> begin
(
# 517 "FStar.SMTEncoding.Encode.fst"
let _77_733 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_77_733) with
| (base_t, decls) -> begin
(
# 518 "FStar.SMTEncoding.Encode.fst"
let _77_737 = (gen_term_var env x)
in (match (_77_737) with
| (x, xtm, env') -> begin
(
# 519 "FStar.SMTEncoding.Encode.fst"
let _77_740 = (encode_formula f env')
in (match (_77_740) with
| (refinement, decls') -> begin
(
# 521 "FStar.SMTEncoding.Encode.fst"
let _77_743 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_77_743) with
| (fsym, fterm) -> begin
(
# 523 "FStar.SMTEncoding.Encode.fst"
let encoding = (let _156_598 = (let _156_597 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_156_597, refinement))
in (FStar_SMTEncoding_Term.mkAnd _156_598))
in (
# 525 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _156_600 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _156_600 (FStar_List.filter (fun _77_748 -> (match (_77_748) with
| (y, _77_747) -> begin
((y <> x) && (y <> fsym))
end)))))
in (
# 526 "FStar.SMTEncoding.Encode.fst"
let xfv = (x, FStar_SMTEncoding_Term.Term_sort)
in (
# 527 "FStar.SMTEncoding.Encode.fst"
let ffv = (fsym, FStar_SMTEncoding_Term.Fuel_sort)
in (
# 528 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _77_755, _77_757) -> begin
(let _156_603 = (let _156_602 = (let _156_601 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t, _156_601))
in (FStar_SMTEncoding_Term.mkApp _156_602))
in (_156_603, []))
end
| None -> begin
(
# 535 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Typ_refine")
in (
# 536 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 537 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (
# 538 "FStar.SMTEncoding.Encode.fst"
let t = (let _156_605 = (let _156_604 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _156_604))
in (FStar_SMTEncoding_Term.mkApp _156_605))
in (
# 540 "FStar.SMTEncoding.Encode.fst"
let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (
# 541 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 543 "FStar.SMTEncoding.Encode.fst"
let t_kinding = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (
# 544 "FStar.SMTEncoding.Encode.fst"
let assumption = (let _156_607 = (let _156_606 = (FStar_SMTEncoding_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _156_606))
in (FStar_SMTEncoding_Term.mkForall _156_607))
in (
# 546 "FStar.SMTEncoding.Encode.fst"
let t_decls = (let _156_614 = (let _156_613 = (let _156_612 = (let _156_611 = (let _156_610 = (let _156_609 = (let _156_608 = (FStar_Syntax_Print.term_to_string t0)
in Some (_156_608))
in (assumption, _156_609))
in FStar_SMTEncoding_Term.Assume (_156_610))
in (_156_611)::[])
in (FStar_SMTEncoding_Term.Assume ((t_kinding, None)))::_156_612)
in (tdecl)::_156_613)
in (FStar_List.append (FStar_List.append decls decls') _156_614))
in (
# 551 "FStar.SMTEncoding.Encode.fst"
let _77_770 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(
# 556 "FStar.SMTEncoding.Encode.fst"
let ttm = (let _156_615 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _156_615))
in (
# 557 "FStar.SMTEncoding.Encode.fst"
let _77_779 = (encode_term_pred None k env ttm)
in (match (_77_779) with
| (t_has_k, decls) -> begin
(
# 558 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_77_782) -> begin
(
# 562 "FStar.SMTEncoding.Encode.fst"
let _77_786 = (FStar_Syntax_Util.head_and_args t0)
in (match (_77_786) with
| (head, args_e) -> begin
(match ((let _156_617 = (let _156_616 = (FStar_Syntax_Subst.compress head)
in _156_616.FStar_Syntax_Syntax.n)
in (_156_617, args_e))) with
| (FStar_Syntax_Syntax.Tm_abs (_77_788), _77_791) -> begin
(let _156_618 = (whnf env t)
in (encode_term _156_618 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (l, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _::(v1, _)::(v2, _)::[])) | ((FStar_Syntax_Syntax.Tm_fvar (l, _), _::(v1, _)::(v2, _)::[])) when (FStar_Ident.lid_equals l.FStar_Syntax_Syntax.v FStar_Syntax_Const.lexcons_lid) -> begin
(
# 569 "FStar.SMTEncoding.Encode.fst"
let _77_837 = (encode_term v1 env)
in (match (_77_837) with
| (v1, decls1) -> begin
(
# 570 "FStar.SMTEncoding.Encode.fst"
let _77_840 = (encode_term v2 env)
in (match (_77_840) with
| (v2, decls2) -> begin
(let _156_619 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in (_156_619, (FStar_List.append decls1 decls2)))
end))
end))
end
| _77_842 -> begin
(
# 574 "FStar.SMTEncoding.Encode.fst"
let _77_845 = (encode_args args_e env)
in (match (_77_845) with
| (args, decls) -> begin
(
# 576 "FStar.SMTEncoding.Encode.fst"
let encode_partial_app = (fun ht_opt -> (
# 577 "FStar.SMTEncoding.Encode.fst"
let _77_850 = (encode_term head env)
in (match (_77_850) with
| (head, decls') -> begin
(
# 578 "FStar.SMTEncoding.Encode.fst"
let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(
# 582 "FStar.SMTEncoding.Encode.fst"
let _77_859 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_77_859) with
| (formals, rest) -> begin
(
# 583 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _77_863 _77_867 -> (match ((_77_863, _77_867)) with
| ((bv, _77_862), (a, _77_866)) -> begin
FStar_Syntax_Syntax.NT ((bv, a))
end)) formals args_e)
in (
# 584 "FStar.SMTEncoding.Encode.fst"
let ty = (let _156_624 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _156_624 (FStar_Syntax_Subst.subst subst)))
in (
# 585 "FStar.SMTEncoding.Encode.fst"
let _77_872 = (encode_term_pred None ty env app_tm)
in (match (_77_872) with
| (has_type, decls'') -> begin
(
# 586 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (
# 587 "FStar.SMTEncoding.Encode.fst"
let e_typing = (let _156_626 = (let _156_625 = (FStar_SMTEncoding_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_156_625, None))
in FStar_SMTEncoding_Term.Assume (_156_626))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (
# 591 "FStar.SMTEncoding.Encode.fst"
let encode_full_app = (fun fv -> (
# 592 "FStar.SMTEncoding.Encode.fst"
let _77_879 = (lookup_free_var_sym env fv)
in (match (_77_879) with
| (fname, fuel_args) -> begin
(
# 593 "FStar.SMTEncoding.Encode.fst"
let tm = (FStar_SMTEncoding_Term.mkApp' (fname, (FStar_List.append fuel_args args)))
in (tm, decls))
end)))
in (
# 596 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Subst.compress head)
in (
# 598 "FStar.SMTEncoding.Encode.fst"
let head_type = (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
x.FStar_Syntax_Syntax.sort
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv, _)) -> begin
(let _156_629 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _156_629 Prims.snd))
end
| FStar_Syntax_Syntax.Tm_ascribed (_77_917, t, _77_920) -> begin
t
end
| _77_924 -> begin
(let _156_633 = (let _156_632 = (FStar_Syntax_Print.term_to_string t0)
in (let _156_631 = (FStar_Syntax_Print.tag_of_term head)
in (let _156_630 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format3 "Unexpected head of application %s is: %s, %s" _156_632 _156_631 _156_630))))
in (FStar_All.failwith _156_633))
end)
in (
# 608 "FStar.SMTEncoding.Encode.fst"
let head_type = (let _156_634 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _156_634))
in (
# 610 "FStar.SMTEncoding.Encode.fst"
let _77_927 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _156_637 = (FStar_Syntax_Print.term_to_string head)
in (let _156_636 = (FStar_Syntax_Print.tag_of_term head)
in (let _156_635 = (FStar_Syntax_Print.term_to_string head_type)
in (FStar_Util.print3 "Recomputed type of head %s (%s) to be %s\n" _156_637 _156_636 _156_635))))
end else begin
()
end
in (
# 613 "FStar.SMTEncoding.Encode.fst"
let _77_931 = (curried_arrow_formals_comp head_type)
in (match (_77_931) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv, _)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _77_953 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some ((formals, c))))
end else begin
(encode_partial_app None)
end
end)
end))))))))
end))
end)
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(
# 626 "FStar.SMTEncoding.Encode.fst"
let _77_962 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_77_962) with
| (bs, body, opening) -> begin
(
# 627 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _77_964 -> (match (()) with
| () -> begin
(
# 628 "FStar.SMTEncoding.Encode.fst"
let f = (varops.fresh "Tm_abs")
in (
# 629 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.DeclFun ((f, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _156_640 = (FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
in (_156_640, (decl)::[]))))
end))
in (match (lopt) with
| None -> begin
(
# 634 "FStar.SMTEncoding.Encode.fst"
let _77_968 = (let _156_642 = (let _156_641 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _156_641))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _156_642))
in (fallback ()))
end
| Some (lc) -> begin
if (let _156_643 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (FStar_All.pipe_left Prims.op_Negation _156_643)) then begin
(fallback ())
end else begin
(
# 640 "FStar.SMTEncoding.Encode.fst"
let c0 = (lc.FStar_Syntax_Syntax.comp ())
in (
# 641 "FStar.SMTEncoding.Encode.fst"
let c = (FStar_Syntax_Subst.subst_comp opening c0)
in (
# 644 "FStar.SMTEncoding.Encode.fst"
let _77_980 = (encode_binders None bs env)
in (match (_77_980) with
| (vars, guards, envbody, decls, _77_979) -> begin
(
# 645 "FStar.SMTEncoding.Encode.fst"
let _77_983 = (encode_term body envbody)
in (match (_77_983) with
| (body, decls') -> begin
(
# 646 "FStar.SMTEncoding.Encode.fst"
let key_body = (let _156_647 = (let _156_646 = (let _156_645 = (let _156_644 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_156_644, body))
in (FStar_SMTEncoding_Term.mkImp _156_645))
in ([], vars, _156_646))
in (FStar_SMTEncoding_Term.mkForall _156_647))
in (
# 647 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (
# 648 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _77_989, _77_991) -> begin
(let _156_650 = (let _156_649 = (let _156_648 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (t, _156_648))
in (FStar_SMTEncoding_Term.mkApp _156_649))
in (_156_650, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
(t, [])
end
| None -> begin
(
# 657 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 658 "FStar.SMTEncoding.Encode.fst"
let fsym = (varops.fresh "Exp_abs")
in (
# 659 "FStar.SMTEncoding.Encode.fst"
let fdecl = FStar_SMTEncoding_Term.DeclFun ((fsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (
# 660 "FStar.SMTEncoding.Encode.fst"
let f = (let _156_652 = (let _156_651 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (fsym, _156_651))
in (FStar_SMTEncoding_Term.mkApp _156_652))
in (
# 661 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 662 "FStar.SMTEncoding.Encode.fst"
let tfun = (FStar_Syntax_Util.arrow bs c)
in (
# 663 "FStar.SMTEncoding.Encode.fst"
let _77_1006 = (encode_term_pred None tfun env f)
in (match (_77_1006) with
| (f_has_t, decls'') -> begin
(
# 664 "FStar.SMTEncoding.Encode.fst"
let typing_f = (let _156_654 = (let _156_653 = (FStar_SMTEncoding_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_156_653, Some ((Prims.strcat fsym " typing"))))
in FStar_SMTEncoding_Term.Assume (_156_654))
in (
# 666 "FStar.SMTEncoding.Encode.fst"
let interp_f = (let _156_661 = (let _156_660 = (let _156_659 = (let _156_658 = (let _156_657 = (let _156_656 = (FStar_SMTEncoding_Term.mk_IsTyped app)
in (let _156_655 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_156_656, _156_655)))
in (FStar_SMTEncoding_Term.mkImp _156_657))
in (((app)::[])::[], (FStar_List.append vars cvars), _156_658))
in (FStar_SMTEncoding_Term.mkForall _156_659))
in (_156_660, Some ((Prims.strcat fsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_156_661))
in (
# 668 "FStar.SMTEncoding.Encode.fst"
let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (
# 669 "FStar.SMTEncoding.Encode.fst"
let _77_1010 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end))))))))
end)
end))))
end))
end))))
end
end))
end))
end
| FStar_Syntax_Syntax.Tm_let ((_77_1013, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_77_1025); FStar_Syntax_Syntax.lbunivs = _77_1023; FStar_Syntax_Syntax.lbtyp = _77_1021; FStar_Syntax_Syntax.lbeff = _77_1019; FStar_Syntax_Syntax.lbdef = _77_1017}::_77_1015), _77_1031) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _77_1040; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _77_1037; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_77_1050) -> begin
(
# 682 "FStar.SMTEncoding.Encode.fst"
let _77_1052 = (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (
# 683 "FStar.SMTEncoding.Encode.fst"
let e = (varops.fresh "let-rec")
in (
# 684 "FStar.SMTEncoding.Encode.fst"
let decl_e = FStar_SMTEncoding_Term.DeclFun ((e, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _156_662 = (FStar_SMTEncoding_Term.mkFreeV (e, FStar_SMTEncoding_Term.Term_sort))
in (_156_662, (decl_e)::[])))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (
# 691 "FStar.SMTEncoding.Encode.fst"
let _77_1068 = (encode_term e1 env)
in (match (_77_1068) with
| (ee1, decls1) -> begin
(
# 692 "FStar.SMTEncoding.Encode.fst"
let _77_1071 = (FStar_Syntax_Subst.open_term (((x, None))::[]) e2)
in (match (_77_1071) with
| (xs, e2) -> begin
(
# 693 "FStar.SMTEncoding.Encode.fst"
let _77_1075 = (FStar_List.hd xs)
in (match (_77_1075) with
| (x, _77_1074) -> begin
(
# 694 "FStar.SMTEncoding.Encode.fst"
let env' = (push_term_var env x ee1)
in (
# 695 "FStar.SMTEncoding.Encode.fst"
let _77_1079 = (encode_term e2 env')
in (match (_77_1079) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (
# 699 "FStar.SMTEncoding.Encode.fst"
let _77_1087 = (encode_term e env)
in (match (_77_1087) with
| (scr, decls) -> begin
(
# 700 "FStar.SMTEncoding.Encode.fst"
let _77_1124 = (FStar_List.fold_right (fun b _77_1091 -> (match (_77_1091) with
| (else_case, decls) -> begin
(
# 701 "FStar.SMTEncoding.Encode.fst"
let _77_1095 = (FStar_Syntax_Subst.open_branch b)
in (match (_77_1095) with
| (p, w, br) -> begin
(
# 702 "FStar.SMTEncoding.Encode.fst"
let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _77_1099 _77_1102 -> (match ((_77_1099, _77_1102)) with
| ((env0, pattern), (else_case, decls)) -> begin
(
# 704 "FStar.SMTEncoding.Encode.fst"
let guard = (pattern.guard scr)
in (
# 705 "FStar.SMTEncoding.Encode.fst"
let projections = (pattern.projections scr)
in (
# 706 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _77_1108 -> (match (_77_1108) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (
# 707 "FStar.SMTEncoding.Encode.fst"
let _77_1118 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(
# 710 "FStar.SMTEncoding.Encode.fst"
let _77_1115 = (encode_term w env)
in (match (_77_1115) with
| (w, decls2) -> begin
(let _156_696 = (let _156_695 = (let _156_694 = (let _156_693 = (let _156_692 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in (w, _156_692))
in (FStar_SMTEncoding_Term.mkEq _156_693))
in (guard, _156_694))
in (FStar_SMTEncoding_Term.mkAnd _156_695))
in (_156_696, decls2))
end))
end)
in (match (_77_1118) with
| (guard, decls2) -> begin
(
# 712 "FStar.SMTEncoding.Encode.fst"
let _77_1121 = (encode_br br env)
in (match (_77_1121) with
| (br, decls3) -> begin
(let _156_697 = (FStar_SMTEncoding_Term.mkITE (guard, br, else_case))
in (_156_697, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end))
end)) pats (default_case, decls))
in (match (_77_1124) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _77_1130 -> begin
(let _156_700 = (encode_one_pat env pat)
in (_156_700)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (
# 726 "FStar.SMTEncoding.Encode.fst"
let _77_1133 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _156_703 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _156_703))
end else begin
()
end
in (
# 727 "FStar.SMTEncoding.Encode.fst"
let _77_1137 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_77_1137) with
| (vars, pat_term) -> begin
(
# 729 "FStar.SMTEncoding.Encode.fst"
let _77_1149 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _77_1140 v -> (match (_77_1140) with
| (env, vars) -> begin
(
# 730 "FStar.SMTEncoding.Encode.fst"
let _77_1146 = (gen_term_var env v)
in (match (_77_1146) with
| (xx, _77_1144, env) -> begin
(env, ((v, (xx, FStar_SMTEncoding_Term.Term_sort)))::vars)
end))
end)) (env, [])))
in (match (_77_1149) with
| (env, vars) -> begin
(
# 733 "FStar.SMTEncoding.Encode.fst"
let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_77_1154) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _156_711 = (let _156_710 = (encode_const c)
in (scrutinee, _156_710))
in (FStar_SMTEncoding_Term.mkEq _156_711))
end
| FStar_Syntax_Syntax.Pat_cons ((f, _77_1169), args) -> begin
(
# 741 "FStar.SMTEncoding.Encode.fst"
let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.v scrutinee)
in (
# 742 "FStar.SMTEncoding.Encode.fst"
let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _77_1179 -> (match (_77_1179) with
| (arg, _77_1178) -> begin
(
# 743 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.v i)
in (let _156_714 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _156_714)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (
# 747 "FStar.SMTEncoding.Encode.fst"
let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_77_1186) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
((x, scrutinee))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_77_1196) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons ((f, _77_1200), args) -> begin
(let _156_722 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _77_1209 -> (match (_77_1209) with
| (arg, _77_1208) -> begin
(
# 759 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.v i)
in (let _156_721 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _156_721)))
end))))
in (FStar_All.pipe_right _156_722 FStar_List.flatten))
end))
in (
# 763 "FStar.SMTEncoding.Encode.fst"
let pat_term = (fun _77_1212 -> (match (()) with
| () -> begin
(encode_term pat_term env)
end))
in (
# 765 "FStar.SMTEncoding.Encode.fst"
let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (
# 775 "FStar.SMTEncoding.Encode.fst"
let _77_1228 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _77_1218 _77_1222 -> (match ((_77_1218, _77_1222)) with
| ((tms, decls), (t, _77_1221)) -> begin
(
# 776 "FStar.SMTEncoding.Encode.fst"
let _77_1225 = (encode_term t env)
in (match (_77_1225) with
| (t, decls') -> begin
((t)::tms, (FStar_List.append decls decls'))
end))
end)) ([], [])))
in (match (_77_1228) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (
# 781 "FStar.SMTEncoding.Encode.fst"
let _77_1234 = (encode_formula_with_labels phi env)
in (match (_77_1234) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _77_1237 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (
# 788 "FStar.SMTEncoding.Encode.fst"
let rec list_elements = (fun e -> (
# 789 "FStar.SMTEncoding.Encode.fst"
let _77_1246 = (let _156_737 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _156_737))
in (match (_77_1246) with
| (head, args) -> begin
(match ((let _156_739 = (let _156_738 = (FStar_Syntax_Util.un_uinst head)
in _156_738.FStar_Syntax_Syntax.n)
in (_156_739, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv, _77_1249), _77_1253) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv, _77_1257), _77_1269::(hd, _77_1266)::(tl, _77_1262)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.cons_lid) -> begin
(let _156_740 = (list_elements tl)
in (hd)::_156_740)
end
| _77_1273 -> begin
(
# 794 "FStar.SMTEncoding.Encode.fst"
let _77_1274 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (
# 796 "FStar.SMTEncoding.Encode.fst"
let v_or_t_pat = (fun p -> (
# 797 "FStar.SMTEncoding.Encode.fst"
let _77_1280 = (let _156_743 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _156_743 FStar_Syntax_Util.head_and_args))
in (match (_77_1280) with
| (head, args) -> begin
(match ((let _156_745 = (let _156_744 = (FStar_Syntax_Util.un_uinst head)
in _156_744.FStar_Syntax_Syntax.n)
in (_156_745, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv, _77_1283), (_77_1291, _77_1293)::(e, _77_1288)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpat_lid) -> begin
(e, None)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv, _77_1299), (t, _77_1304)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpatT_lid) -> begin
(t, None)
end
| _77_1309 -> begin
(FStar_All.failwith "Unexpected pattern term")
end)
end)))
in (
# 803 "FStar.SMTEncoding.Encode.fst"
let lemma_pats = (fun p -> (
# 804 "FStar.SMTEncoding.Encode.fst"
let elts = (list_elements p)
in (
# 805 "FStar.SMTEncoding.Encode.fst"
let smt_pat_or = (fun t -> (
# 806 "FStar.SMTEncoding.Encode.fst"
let _77_1317 = (let _156_750 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _156_750 FStar_Syntax_Util.head_and_args))
in (match (_77_1317) with
| (head, args) -> begin
(match ((let _156_752 = (let _156_751 = (FStar_Syntax_Util.un_uinst head)
in _156_751.FStar_Syntax_Syntax.n)
in (_156_752, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv, _77_1320), (e, _77_1325)::[]) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _77_1330 -> begin
None
end)
end)))
in (match (elts) with
| t::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _156_755 = (list_elements e)
in (FStar_All.pipe_right _156_755 (FStar_List.map (fun branch -> (let _156_754 = (list_elements branch)
in (FStar_All.pipe_right _156_754 (FStar_List.map v_or_t_pat)))))))
end
| _77_1337 -> begin
(let _156_756 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_156_756)::[])
end)
end
| _77_1339 -> begin
(let _156_757 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_156_757)::[])
end))))
in (
# 820 "FStar.SMTEncoding.Encode.fst"
let _77_1373 = (match ((let _156_758 = (FStar_Syntax_Subst.compress t)
in _156_758.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 822 "FStar.SMTEncoding.Encode.fst"
let _77_1346 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_77_1346) with
| (binders, c) -> begin
(
# 823 "FStar.SMTEncoding.Encode.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre, _77_1358)::(post, _77_1354)::(pats, _77_1350)::[] -> begin
(
# 826 "FStar.SMTEncoding.Encode.fst"
let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _156_759 = (lemma_pats pats')
in (binders, pre, post, _156_759)))
end
| _77_1366 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _77_1368 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_77_1373) with
| (binders, pre, post, patterns) -> begin
(
# 834 "FStar.SMTEncoding.Encode.fst"
let _77_1380 = (encode_binders None binders env)
in (match (_77_1380) with
| (vars, guards, env, decls, _77_1379) -> begin
(
# 837 "FStar.SMTEncoding.Encode.fst"
let _77_1393 = (let _156_763 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (
# 838 "FStar.SMTEncoding.Encode.fst"
let _77_1390 = (let _156_762 = (FStar_All.pipe_right branch (FStar_List.map (fun _77_1385 -> (match (_77_1385) with
| (t, _77_1384) -> begin
(encode_term t (
# 838 "FStar.SMTEncoding.Encode.fst"
let _77_1386 = env
in {bindings = _77_1386.bindings; depth = _77_1386.depth; tcenv = _77_1386.tcenv; warn = _77_1386.warn; cache = _77_1386.cache; nolabels = _77_1386.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _77_1386.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _156_762 FStar_List.unzip))
in (match (_77_1390) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _156_763 FStar_List.unzip))
in (match (_77_1393) with
| (pats, decls') -> begin
(
# 841 "FStar.SMTEncoding.Encode.fst"
let decls' = (FStar_List.flatten decls')
in (
# 843 "FStar.SMTEncoding.Encode.fst"
let pats = (match (induction_on) with
| None -> begin
pats
end
| Some (e) -> begin
(match (vars) with
| [] -> begin
pats
end
| l::[] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _156_766 = (let _156_765 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _156_765 e))
in (_156_766)::p))))
end
| _77_1403 -> begin
(
# 851 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _156_772 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_156_772)::p))))
end
| (x, FStar_SMTEncoding_Term.Term_sort)::vars -> begin
(let _156_774 = (let _156_773 = (FStar_SMTEncoding_Term.mkFreeV (x, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_LexCons _156_773 tl))
in (aux _156_774 vars))
end
| _77_1415 -> begin
pats
end))
in (let _156_775 = (FStar_SMTEncoding_Term.mkFreeV ("Prims.LexTop", FStar_SMTEncoding_Term.Term_sort))
in (aux _156_775 vars)))
end)
end)
in (
# 858 "FStar.SMTEncoding.Encode.fst"
let env = (
# 858 "FStar.SMTEncoding.Encode.fst"
let _77_1417 = env
in {bindings = _77_1417.bindings; depth = _77_1417.depth; tcenv = _77_1417.tcenv; warn = _77_1417.warn; cache = _77_1417.cache; nolabels = true; use_zfuel_name = _77_1417.use_zfuel_name; encode_non_total_function_typ = _77_1417.encode_non_total_function_typ})
in (
# 859 "FStar.SMTEncoding.Encode.fst"
let _77_1422 = (let _156_776 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _156_776 env))
in (match (_77_1422) with
| (pre, decls'') -> begin
(
# 860 "FStar.SMTEncoding.Encode.fst"
let _77_1425 = (let _156_777 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _156_777 env))
in (match (_77_1425) with
| (post, decls''') -> begin
(
# 861 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _156_782 = (let _156_781 = (let _156_780 = (let _156_779 = (let _156_778 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in (_156_778, post))
in (FStar_SMTEncoding_Term.mkImp _156_779))
in (pats, vars, _156_780))
in (FStar_SMTEncoding_Term.mkForall _156_781))
in (_156_782, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula_with_labels : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * labels * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (
# 865 "FStar.SMTEncoding.Encode.fst"
let enc = (fun f l -> (
# 866 "FStar.SMTEncoding.Encode.fst"
let _77_1439 = (FStar_Util.fold_map (fun decls x -> (
# 866 "FStar.SMTEncoding.Encode.fst"
let _77_1436 = (encode_term (Prims.fst x) env)
in (match (_77_1436) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))) [] l)
in (match (_77_1439) with
| (decls, args) -> begin
(let _156_800 = (f args)
in (_156_800, [], decls))
end)))
in (
# 869 "FStar.SMTEncoding.Encode.fst"
let const_op = (fun f _77_1442 -> (f, [], []))
in (
# 870 "FStar.SMTEncoding.Encode.fst"
let un_op = (fun f l -> (let _156_814 = (FStar_List.hd l)
in (FStar_All.pipe_left f _156_814)))
in (
# 871 "FStar.SMTEncoding.Encode.fst"
let bin_op = (fun f _77_8 -> (match (_77_8) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _77_1453 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 875 "FStar.SMTEncoding.Encode.fst"
let enc_prop_c = (fun f l -> (
# 876 "FStar.SMTEncoding.Encode.fst"
let _77_1473 = (FStar_List.fold_right (fun _77_1461 _77_1465 -> (match ((_77_1461, _77_1465)) with
| ((t, _77_1460), (phis, labs, decls)) -> begin
(
# 878 "FStar.SMTEncoding.Encode.fst"
let _77_1469 = (encode_formula_with_labels t env)
in (match (_77_1469) with
| (phi, labs', decls') -> begin
((phi)::phis, (FStar_List.append labs' labs), (FStar_List.append decls' decls))
end))
end)) l ([], [], []))
in (match (_77_1473) with
| (phis, labs, decls) -> begin
(let _156_839 = (f phis)
in (_156_839, labs, decls))
end)))
in (
# 883 "FStar.SMTEncoding.Encode.fst"
let eq_op = (fun _77_9 -> (match (_77_9) with
| _77_1480::_77_1478::e1::e2::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (
# 887 "FStar.SMTEncoding.Encode.fst"
let mk_imp = (fun _77_10 -> (match (_77_10) with
| (lhs, _77_1491)::(rhs, _77_1487)::[] -> begin
(
# 889 "FStar.SMTEncoding.Encode.fst"
let _77_1497 = (encode_formula_with_labels rhs env)
in (match (_77_1497) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _77_1500) -> begin
(l1, labs1, decls1)
end
| _77_1504 -> begin
(
# 893 "FStar.SMTEncoding.Encode.fst"
let _77_1508 = (encode_formula_with_labels lhs env)
in (match (_77_1508) with
| (l2, labs2, decls2) -> begin
(let _156_844 = (FStar_SMTEncoding_Term.mkImp (l2, l1))
in (_156_844, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _77_1510 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 898 "FStar.SMTEncoding.Encode.fst"
let mk_ite = (fun _77_11 -> (match (_77_11) with
| (guard, _77_1523)::(_then, _77_1519)::(_else, _77_1515)::[] -> begin
(
# 900 "FStar.SMTEncoding.Encode.fst"
let _77_1529 = (encode_formula_with_labels guard env)
in (match (_77_1529) with
| (g, labs1, decls1) -> begin
(
# 901 "FStar.SMTEncoding.Encode.fst"
let _77_1533 = (encode_formula_with_labels _then env)
in (match (_77_1533) with
| (t, labs2, decls2) -> begin
(
# 902 "FStar.SMTEncoding.Encode.fst"
let _77_1537 = (encode_formula_with_labels _else env)
in (match (_77_1537) with
| (e, labs3, decls3) -> begin
(
# 903 "FStar.SMTEncoding.Encode.fst"
let res = (FStar_SMTEncoding_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append labs1 labs2) labs3), (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _77_1540 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 908 "FStar.SMTEncoding.Encode.fst"
let unboxInt_l = (fun f l -> (let _156_856 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _156_856)))
in (
# 909 "FStar.SMTEncoding.Encode.fst"
let connectives = (let _156_909 = (let _156_865 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in (FStar_Syntax_Const.and_lid, _156_865))
in (let _156_908 = (let _156_907 = (let _156_871 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in (FStar_Syntax_Const.or_lid, _156_871))
in (let _156_906 = (let _156_905 = (let _156_904 = (let _156_880 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in (FStar_Syntax_Const.iff_lid, _156_880))
in (let _156_903 = (let _156_902 = (let _156_901 = (let _156_889 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in (FStar_Syntax_Const.not_lid, _156_889))
in (_156_901)::((FStar_Syntax_Const.eq2_lid, eq_op))::((FStar_Syntax_Const.true_lid, (const_op FStar_SMTEncoding_Term.mkTrue)))::((FStar_Syntax_Const.false_lid, (const_op FStar_SMTEncoding_Term.mkFalse)))::[])
in ((FStar_Syntax_Const.ite_lid, mk_ite))::_156_902)
in (_156_904)::_156_903))
in ((FStar_Syntax_Const.imp_lid, mk_imp))::_156_905)
in (_156_907)::_156_906))
in (_156_909)::_156_908))
in (
# 921 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(
# 923 "FStar.SMTEncoding.Encode.fst"
let _77_1559 = (encode_formula_with_labels phi' env)
in (match (_77_1559) with
| (phi, labs, decls) -> begin
(let _156_912 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled ((phi, msg, r))))
in (_156_912, [], decls))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(
# 927 "FStar.SMTEncoding.Encode.fst"
let _77_1566 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_77_1566) with
| (t, decls) -> begin
(t, [], decls)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _77_1573; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _77_1570; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 931 "FStar.SMTEncoding.Encode.fst"
let _77_1584 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_77_1584) with
| (t, decls) -> begin
(t, [], decls)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, _77_1595::(x, _77_1592)::(t, _77_1588)::[]) -> begin
(
# 935 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Util.un_uinst head)
in (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _77_1602) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.has_type_lid) -> begin
(
# 938 "FStar.SMTEncoding.Encode.fst"
let _77_1607 = (encode_term x env)
in (match (_77_1607) with
| (x, decls) -> begin
(
# 939 "FStar.SMTEncoding.Encode.fst"
let _77_1610 = (encode_term t env)
in (match (_77_1610) with
| (t, decls') -> begin
(let _156_913 = (FStar_SMTEncoding_Term.mk_HasType x t)
in (_156_913, [], (FStar_List.append decls decls')))
end))
end))
end
| _77_1612 -> begin
(
# 942 "FStar.SMTEncoding.Encode.fst"
let _77_1615 = (encode_term phi env)
in (match (_77_1615) with
| (tt, decls) -> begin
(let _156_914 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_156_914, [], decls))
end))
end))
end
| _77_1617 -> begin
(
# 947 "FStar.SMTEncoding.Encode.fst"
let _77_1620 = (encode_term phi env)
in (match (_77_1620) with
| (tt, decls) -> begin
(let _156_915 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_156_915, [], decls))
end))
end))
in (
# 950 "FStar.SMTEncoding.Encode.fst"
let encode_q_body = (fun env bs ps body -> (
# 951 "FStar.SMTEncoding.Encode.fst"
let _77_1632 = (encode_binders None bs env)
in (match (_77_1632) with
| (vars, guards, env, decls, _77_1631) -> begin
(
# 952 "FStar.SMTEncoding.Encode.fst"
let _77_1645 = (let _156_927 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (
# 953 "FStar.SMTEncoding.Encode.fst"
let _77_1642 = (let _156_926 = (FStar_All.pipe_right p (FStar_List.map (fun _77_1637 -> (match (_77_1637) with
| (t, _77_1636) -> begin
(encode_term t (
# 953 "FStar.SMTEncoding.Encode.fst"
let _77_1638 = env
in {bindings = _77_1638.bindings; depth = _77_1638.depth; tcenv = _77_1638.tcenv; warn = _77_1638.warn; cache = _77_1638.cache; nolabels = _77_1638.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _77_1638.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _156_926 FStar_List.unzip))
in (match (_77_1642) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _156_927 FStar_List.unzip))
in (match (_77_1645) with
| (pats, decls') -> begin
(
# 955 "FStar.SMTEncoding.Encode.fst"
let _77_1649 = (encode_formula_with_labels body env)
in (match (_77_1649) with
| (body, labs, decls'') -> begin
(let _156_928 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (vars, pats, _156_928, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (
# 958 "FStar.SMTEncoding.Encode.fst"
let _77_1650 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _156_929 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print1 ">>>> Destructing as formula ... %s\n" _156_929))
end else begin
()
end
in (
# 960 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _77_1662 -> (match (_77_1662) with
| (l, _77_1661) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_77_1665, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(
# 970 "FStar.SMTEncoding.Encode.fst"
let _77_1675 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _156_946 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _156_946))
end else begin
()
end
in (
# 973 "FStar.SMTEncoding.Encode.fst"
let _77_1683 = (encode_q_body env vars pats body)
in (match (_77_1683) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _156_949 = (let _156_948 = (let _156_947 = (FStar_SMTEncoding_Term.mkImp (guard, body))
in (pats, vars, _156_947))
in (FStar_SMTEncoding_Term.mkForall _156_948))
in (_156_949, labs, decls))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(
# 977 "FStar.SMTEncoding.Encode.fst"
let _77_1696 = (encode_q_body env vars pats body)
in (match (_77_1696) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _156_952 = (let _156_951 = (let _156_950 = (FStar_SMTEncoding_Term.mkAnd (guard, body))
in (pats, vars, _156_950))
in (FStar_SMTEncoding_Term.mkExists _156_951))
in (_156_952, labs, decls))
end))
end))))))))))))))))

# 986 "FStar.SMTEncoding.Encode.fst"
type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}

# 986 "FStar.SMTEncoding.Encode.fst"
let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))

# 992 "FStar.SMTEncoding.Encode.fst"
let prims : prims_t = (
# 993 "FStar.SMTEncoding.Encode.fst"
let _77_1702 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_77_1702) with
| (asym, a) -> begin
(
# 994 "FStar.SMTEncoding.Encode.fst"
let _77_1705 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_77_1705) with
| (xsym, x) -> begin
(
# 995 "FStar.SMTEncoding.Encode.fst"
let _77_1708 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_77_1708) with
| (ysym, y) -> begin
(
# 996 "FStar.SMTEncoding.Encode.fst"
let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun ((x, vars, FStar_SMTEncoding_Term.Term_sort, body, None)))::[])
in (
# 997 "FStar.SMTEncoding.Encode.fst"
let quant = (fun vars body x -> (
# 998 "FStar.SMTEncoding.Encode.fst"
let t1 = (let _156_995 = (let _156_994 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (x, _156_994))
in (FStar_SMTEncoding_Term.mkApp _156_995))
in (
# 999 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _156_997 = (let _156_996 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _156_996, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_156_997))
in (let _156_1003 = (let _156_1002 = (let _156_1001 = (let _156_1000 = (let _156_999 = (let _156_998 = (FStar_SMTEncoding_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _156_998))
in (FStar_SMTEncoding_Term.mkForall _156_999))
in (_156_1000, None))
in FStar_SMTEncoding_Term.Assume (_156_1001))
in (_156_1002)::[])
in (vname_decl)::_156_1003))))
in (
# 1002 "FStar.SMTEncoding.Encode.fst"
let axy = ((asym, FStar_SMTEncoding_Term.Term_sort))::((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1003 "FStar.SMTEncoding.Encode.fst"
let xy = ((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1004 "FStar.SMTEncoding.Encode.fst"
let qx = ((xsym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1005 "FStar.SMTEncoding.Encode.fst"
let prims = (let _156_1163 = (let _156_1012 = (let _156_1011 = (let _156_1010 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1010))
in (quant axy _156_1011))
in (FStar_Syntax_Const.op_Eq, _156_1012))
in (let _156_1162 = (let _156_1161 = (let _156_1019 = (let _156_1018 = (let _156_1017 = (let _156_1016 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_SMTEncoding_Term.mkNot _156_1016))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1017))
in (quant axy _156_1018))
in (FStar_Syntax_Const.op_notEq, _156_1019))
in (let _156_1160 = (let _156_1159 = (let _156_1028 = (let _156_1027 = (let _156_1026 = (let _156_1025 = (let _156_1024 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1023 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1024, _156_1023)))
in (FStar_SMTEncoding_Term.mkLT _156_1025))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1026))
in (quant xy _156_1027))
in (FStar_Syntax_Const.op_LT, _156_1028))
in (let _156_1158 = (let _156_1157 = (let _156_1037 = (let _156_1036 = (let _156_1035 = (let _156_1034 = (let _156_1033 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1032 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1033, _156_1032)))
in (FStar_SMTEncoding_Term.mkLTE _156_1034))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1035))
in (quant xy _156_1036))
in (FStar_Syntax_Const.op_LTE, _156_1037))
in (let _156_1156 = (let _156_1155 = (let _156_1046 = (let _156_1045 = (let _156_1044 = (let _156_1043 = (let _156_1042 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1041 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1042, _156_1041)))
in (FStar_SMTEncoding_Term.mkGT _156_1043))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1044))
in (quant xy _156_1045))
in (FStar_Syntax_Const.op_GT, _156_1046))
in (let _156_1154 = (let _156_1153 = (let _156_1055 = (let _156_1054 = (let _156_1053 = (let _156_1052 = (let _156_1051 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1050 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1051, _156_1050)))
in (FStar_SMTEncoding_Term.mkGTE _156_1052))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1053))
in (quant xy _156_1054))
in (FStar_Syntax_Const.op_GTE, _156_1055))
in (let _156_1152 = (let _156_1151 = (let _156_1064 = (let _156_1063 = (let _156_1062 = (let _156_1061 = (let _156_1060 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1059 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1060, _156_1059)))
in (FStar_SMTEncoding_Term.mkSub _156_1061))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _156_1062))
in (quant xy _156_1063))
in (FStar_Syntax_Const.op_Subtraction, _156_1064))
in (let _156_1150 = (let _156_1149 = (let _156_1071 = (let _156_1070 = (let _156_1069 = (let _156_1068 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _156_1068))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _156_1069))
in (quant qx _156_1070))
in (FStar_Syntax_Const.op_Minus, _156_1071))
in (let _156_1148 = (let _156_1147 = (let _156_1080 = (let _156_1079 = (let _156_1078 = (let _156_1077 = (let _156_1076 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1075 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1076, _156_1075)))
in (FStar_SMTEncoding_Term.mkAdd _156_1077))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _156_1078))
in (quant xy _156_1079))
in (FStar_Syntax_Const.op_Addition, _156_1080))
in (let _156_1146 = (let _156_1145 = (let _156_1089 = (let _156_1088 = (let _156_1087 = (let _156_1086 = (let _156_1085 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1084 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1085, _156_1084)))
in (FStar_SMTEncoding_Term.mkMul _156_1086))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _156_1087))
in (quant xy _156_1088))
in (FStar_Syntax_Const.op_Multiply, _156_1089))
in (let _156_1144 = (let _156_1143 = (let _156_1098 = (let _156_1097 = (let _156_1096 = (let _156_1095 = (let _156_1094 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1093 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1094, _156_1093)))
in (FStar_SMTEncoding_Term.mkDiv _156_1095))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _156_1096))
in (quant xy _156_1097))
in (FStar_Syntax_Const.op_Division, _156_1098))
in (let _156_1142 = (let _156_1141 = (let _156_1107 = (let _156_1106 = (let _156_1105 = (let _156_1104 = (let _156_1103 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1102 = (FStar_SMTEncoding_Term.unboxInt y)
in (_156_1103, _156_1102)))
in (FStar_SMTEncoding_Term.mkMod _156_1104))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _156_1105))
in (quant xy _156_1106))
in (FStar_Syntax_Const.op_Modulus, _156_1107))
in (let _156_1140 = (let _156_1139 = (let _156_1116 = (let _156_1115 = (let _156_1114 = (let _156_1113 = (let _156_1112 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _156_1111 = (FStar_SMTEncoding_Term.unboxBool y)
in (_156_1112, _156_1111)))
in (FStar_SMTEncoding_Term.mkAnd _156_1113))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1114))
in (quant xy _156_1115))
in (FStar_Syntax_Const.op_And, _156_1116))
in (let _156_1138 = (let _156_1137 = (let _156_1125 = (let _156_1124 = (let _156_1123 = (let _156_1122 = (let _156_1121 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _156_1120 = (FStar_SMTEncoding_Term.unboxBool y)
in (_156_1121, _156_1120)))
in (FStar_SMTEncoding_Term.mkOr _156_1122))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1123))
in (quant xy _156_1124))
in (FStar_Syntax_Const.op_Or, _156_1125))
in (let _156_1136 = (let _156_1135 = (let _156_1132 = (let _156_1131 = (let _156_1130 = (let _156_1129 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _156_1129))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1130))
in (quant qx _156_1131))
in (FStar_Syntax_Const.op_Negation, _156_1132))
in (_156_1135)::[])
in (_156_1137)::_156_1136))
in (_156_1139)::_156_1138))
in (_156_1141)::_156_1140))
in (_156_1143)::_156_1142))
in (_156_1145)::_156_1144))
in (_156_1147)::_156_1146))
in (_156_1149)::_156_1148))
in (_156_1151)::_156_1150))
in (_156_1153)::_156_1152))
in (_156_1155)::_156_1154))
in (_156_1157)::_156_1156))
in (_156_1159)::_156_1158))
in (_156_1161)::_156_1160))
in (_156_1163)::_156_1162))
in (
# 1022 "FStar.SMTEncoding.Encode.fst"
let mk = (fun l v -> (let _156_1195 = (FStar_All.pipe_right prims (FStar_List.filter (fun _77_1728 -> (match (_77_1728) with
| (l', _77_1727) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _156_1195 (FStar_List.collect (fun _77_1732 -> (match (_77_1732) with
| (_77_1730, b) -> begin
(b v)
end))))))
in (
# 1024 "FStar.SMTEncoding.Encode.fst"
let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _77_1738 -> (match (_77_1738) with
| (l', _77_1737) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

# 1029 "FStar.SMTEncoding.Encode.fst"
let primitive_type_axioms : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (
# 1030 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1031 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1033 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1034 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1036 "FStar.SMTEncoding.Encode.fst"
let mk_unit = (fun _77_1744 tt -> (
# 1037 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _156_1227 = (let _156_1218 = (let _156_1217 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in (_156_1217, Some ("unit typing")))
in FStar_SMTEncoding_Term.Assume (_156_1218))
in (let _156_1226 = (let _156_1225 = (let _156_1224 = (let _156_1223 = (let _156_1222 = (let _156_1221 = (let _156_1220 = (let _156_1219 = (FStar_SMTEncoding_Term.mkEq (x, FStar_SMTEncoding_Term.mk_Term_unit))
in (typing_pred, _156_1219))
in (FStar_SMTEncoding_Term.mkImp _156_1220))
in (((typing_pred)::[])::[], (xx)::[], _156_1221))
in (mkForall_fuel _156_1222))
in (_156_1223, Some ("unit inversion")))
in FStar_SMTEncoding_Term.Assume (_156_1224))
in (_156_1225)::[])
in (_156_1227)::_156_1226))))
in (
# 1040 "FStar.SMTEncoding.Encode.fst"
let mk_bool = (fun _77_1749 tt -> (
# 1041 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1042 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)
in (
# 1043 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _156_1248 = (let _156_1237 = (let _156_1236 = (let _156_1235 = (let _156_1234 = (let _156_1233 = (let _156_1232 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in (typing_pred, _156_1232))
in (FStar_SMTEncoding_Term.mkImp _156_1233))
in (((typing_pred)::[])::[], (xx)::[], _156_1234))
in (mkForall_fuel _156_1235))
in (_156_1236, Some ("bool inversion")))
in FStar_SMTEncoding_Term.Assume (_156_1237))
in (let _156_1247 = (let _156_1246 = (let _156_1245 = (let _156_1244 = (let _156_1243 = (let _156_1242 = (let _156_1239 = (let _156_1238 = (FStar_SMTEncoding_Term.boxBool b)
in (_156_1238)::[])
in (_156_1239)::[])
in (let _156_1241 = (let _156_1240 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _156_1240 tt))
in (_156_1242, (bb)::[], _156_1241)))
in (FStar_SMTEncoding_Term.mkForall _156_1243))
in (_156_1244, Some ("bool typing")))
in FStar_SMTEncoding_Term.Assume (_156_1245))
in (_156_1246)::[])
in (_156_1248)::_156_1247))))))
in (
# 1046 "FStar.SMTEncoding.Encode.fst"
let mk_int = (fun _77_1756 tt -> (
# 1047 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1048 "FStar.SMTEncoding.Encode.fst"
let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (
# 1049 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Int_sort)
in (
# 1050 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1051 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Int_sort)
in (
# 1052 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1053 "FStar.SMTEncoding.Encode.fst"
let precedes = (let _156_1260 = (let _156_1259 = (let _156_1258 = (let _156_1257 = (let _156_1256 = (let _156_1255 = (FStar_SMTEncoding_Term.boxInt a)
in (let _156_1254 = (let _156_1253 = (FStar_SMTEncoding_Term.boxInt b)
in (_156_1253)::[])
in (_156_1255)::_156_1254))
in (tt)::_156_1256)
in (tt)::_156_1257)
in ("Prims.Precedes", _156_1258))
in (FStar_SMTEncoding_Term.mkApp _156_1259))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _156_1260))
in (
# 1054 "FStar.SMTEncoding.Encode.fst"
let precedes_y_x = (let _156_1261 = (FStar_SMTEncoding_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _156_1261))
in (let _156_1303 = (let _156_1267 = (let _156_1266 = (let _156_1265 = (let _156_1264 = (let _156_1263 = (let _156_1262 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in (typing_pred, _156_1262))
in (FStar_SMTEncoding_Term.mkImp _156_1263))
in (((typing_pred)::[])::[], (xx)::[], _156_1264))
in (mkForall_fuel _156_1265))
in (_156_1266, Some ("int inversion")))
in FStar_SMTEncoding_Term.Assume (_156_1267))
in (let _156_1302 = (let _156_1301 = (let _156_1275 = (let _156_1274 = (let _156_1273 = (let _156_1272 = (let _156_1269 = (let _156_1268 = (FStar_SMTEncoding_Term.boxInt b)
in (_156_1268)::[])
in (_156_1269)::[])
in (let _156_1271 = (let _156_1270 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _156_1270 tt))
in (_156_1272, (bb)::[], _156_1271)))
in (FStar_SMTEncoding_Term.mkForall _156_1273))
in (_156_1274, Some ("int typing")))
in FStar_SMTEncoding_Term.Assume (_156_1275))
in (let _156_1300 = (let _156_1299 = (let _156_1298 = (let _156_1297 = (let _156_1296 = (let _156_1295 = (let _156_1294 = (let _156_1293 = (let _156_1292 = (let _156_1291 = (let _156_1290 = (let _156_1289 = (let _156_1278 = (let _156_1277 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _156_1276 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_156_1277, _156_1276)))
in (FStar_SMTEncoding_Term.mkGT _156_1278))
in (let _156_1288 = (let _156_1287 = (let _156_1281 = (let _156_1280 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _156_1279 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_156_1280, _156_1279)))
in (FStar_SMTEncoding_Term.mkGTE _156_1281))
in (let _156_1286 = (let _156_1285 = (let _156_1284 = (let _156_1283 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _156_1282 = (FStar_SMTEncoding_Term.unboxInt x)
in (_156_1283, _156_1282)))
in (FStar_SMTEncoding_Term.mkLT _156_1284))
in (_156_1285)::[])
in (_156_1287)::_156_1286))
in (_156_1289)::_156_1288))
in (typing_pred_y)::_156_1290)
in (typing_pred)::_156_1291)
in (FStar_SMTEncoding_Term.mk_and_l _156_1292))
in (_156_1293, precedes_y_x))
in (FStar_SMTEncoding_Term.mkImp _156_1294))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _156_1295))
in (mkForall_fuel _156_1296))
in (_156_1297, Some ("well-founded ordering on nat (alt)")))
in FStar_SMTEncoding_Term.Assume (_156_1298))
in (_156_1299)::[])
in (_156_1301)::_156_1300))
in (_156_1303)::_156_1302)))))))))))
in (
# 1066 "FStar.SMTEncoding.Encode.fst"
let mk_int_alias = (fun _77_1768 tt -> (let _156_1312 = (let _156_1311 = (let _156_1310 = (let _156_1309 = (let _156_1308 = (FStar_SMTEncoding_Term.mkApp (FStar_Syntax_Const.int_lid.FStar_Ident.str, []))
in (tt, _156_1308))
in (FStar_SMTEncoding_Term.mkEq _156_1309))
in (_156_1310, Some ("mapping to int; for now")))
in FStar_SMTEncoding_Term.Assume (_156_1311))
in (_156_1312)::[]))
in (
# 1068 "FStar.SMTEncoding.Encode.fst"
let mk_str = (fun _77_1772 tt -> (
# 1069 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1070 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.String_sort)
in (
# 1071 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _156_1333 = (let _156_1322 = (let _156_1321 = (let _156_1320 = (let _156_1319 = (let _156_1318 = (let _156_1317 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in (typing_pred, _156_1317))
in (FStar_SMTEncoding_Term.mkImp _156_1318))
in (((typing_pred)::[])::[], (xx)::[], _156_1319))
in (mkForall_fuel _156_1320))
in (_156_1321, Some ("string inversion")))
in FStar_SMTEncoding_Term.Assume (_156_1322))
in (let _156_1332 = (let _156_1331 = (let _156_1330 = (let _156_1329 = (let _156_1328 = (let _156_1327 = (let _156_1324 = (let _156_1323 = (FStar_SMTEncoding_Term.boxString b)
in (_156_1323)::[])
in (_156_1324)::[])
in (let _156_1326 = (let _156_1325 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _156_1325 tt))
in (_156_1327, (bb)::[], _156_1326)))
in (FStar_SMTEncoding_Term.mkForall _156_1328))
in (_156_1329, Some ("string typing")))
in FStar_SMTEncoding_Term.Assume (_156_1330))
in (_156_1331)::[])
in (_156_1333)::_156_1332))))))
in (
# 1074 "FStar.SMTEncoding.Encode.fst"
let mk_ref = (fun reft_name _77_1780 -> (
# 1075 "FStar.SMTEncoding.Encode.fst"
let r = ("r", FStar_SMTEncoding_Term.Ref_sort)
in (
# 1076 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1077 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1078 "FStar.SMTEncoding.Encode.fst"
let refa = (let _156_1340 = (let _156_1339 = (let _156_1338 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_156_1338)::[])
in (reft_name, _156_1339))
in (FStar_SMTEncoding_Term.mkApp _156_1340))
in (
# 1079 "FStar.SMTEncoding.Encode.fst"
let refb = (let _156_1343 = (let _156_1342 = (let _156_1341 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_156_1341)::[])
in (reft_name, _156_1342))
in (FStar_SMTEncoding_Term.mkApp _156_1343))
in (
# 1080 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (
# 1081 "FStar.SMTEncoding.Encode.fst"
let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _156_1362 = (let _156_1349 = (let _156_1348 = (let _156_1347 = (let _156_1346 = (let _156_1345 = (let _156_1344 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in (typing_pred, _156_1344))
in (FStar_SMTEncoding_Term.mkImp _156_1345))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _156_1346))
in (mkForall_fuel _156_1347))
in (_156_1348, Some ("ref inversion")))
in FStar_SMTEncoding_Term.Assume (_156_1349))
in (let _156_1361 = (let _156_1360 = (let _156_1359 = (let _156_1358 = (let _156_1357 = (let _156_1356 = (let _156_1355 = (let _156_1354 = (FStar_SMTEncoding_Term.mkAnd (typing_pred, typing_pred_b))
in (let _156_1353 = (let _156_1352 = (let _156_1351 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _156_1350 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_156_1351, _156_1350)))
in (FStar_SMTEncoding_Term.mkEq _156_1352))
in (_156_1354, _156_1353)))
in (FStar_SMTEncoding_Term.mkImp _156_1355))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _156_1356))
in (mkForall_fuel' 2 _156_1357))
in (_156_1358, Some ("ref typing is injective")))
in FStar_SMTEncoding_Term.Assume (_156_1359))
in (_156_1360)::[])
in (_156_1362)::_156_1361))))))))))
in (
# 1085 "FStar.SMTEncoding.Encode.fst"
let mk_false_interp = (fun _77_1790 false_tm -> (
# 1086 "FStar.SMTEncoding.Encode.fst"
let valid = (FStar_SMTEncoding_Term.mkApp ("Valid", (false_tm)::[]))
in (let _156_1369 = (let _156_1368 = (let _156_1367 = (FStar_SMTEncoding_Term.mkIff (FStar_SMTEncoding_Term.mkFalse, valid))
in (_156_1367, Some ("False interpretation")))
in FStar_SMTEncoding_Term.Assume (_156_1368))
in (_156_1369)::[])))
in (
# 1088 "FStar.SMTEncoding.Encode.fst"
let mk_and_interp = (fun conj _77_1796 -> (
# 1089 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1090 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1091 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1092 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1093 "FStar.SMTEncoding.Encode.fst"
let valid = (let _156_1376 = (let _156_1375 = (let _156_1374 = (FStar_SMTEncoding_Term.mkApp (conj, (a)::(b)::[]))
in (_156_1374)::[])
in ("Valid", _156_1375))
in (FStar_SMTEncoding_Term.mkApp _156_1376))
in (
# 1094 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1095 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _156_1383 = (let _156_1382 = (let _156_1381 = (let _156_1380 = (let _156_1379 = (let _156_1378 = (let _156_1377 = (FStar_SMTEncoding_Term.mkAnd (valid_a, valid_b))
in (_156_1377, valid))
in (FStar_SMTEncoding_Term.mkIff _156_1378))
in (((valid)::[])::[], (aa)::(bb)::[], _156_1379))
in (FStar_SMTEncoding_Term.mkForall _156_1380))
in (_156_1381, Some ("/\\ interpretation")))
in FStar_SMTEncoding_Term.Assume (_156_1382))
in (_156_1383)::[])))))))))
in (
# 1097 "FStar.SMTEncoding.Encode.fst"
let mk_or_interp = (fun disj _77_1807 -> (
# 1098 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1099 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1100 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1101 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1102 "FStar.SMTEncoding.Encode.fst"
let valid = (let _156_1390 = (let _156_1389 = (let _156_1388 = (FStar_SMTEncoding_Term.mkApp (disj, (a)::(b)::[]))
in (_156_1388)::[])
in ("Valid", _156_1389))
in (FStar_SMTEncoding_Term.mkApp _156_1390))
in (
# 1103 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1104 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _156_1397 = (let _156_1396 = (let _156_1395 = (let _156_1394 = (let _156_1393 = (let _156_1392 = (let _156_1391 = (FStar_SMTEncoding_Term.mkOr (valid_a, valid_b))
in (_156_1391, valid))
in (FStar_SMTEncoding_Term.mkIff _156_1392))
in (((valid)::[])::[], (aa)::(bb)::[], _156_1393))
in (FStar_SMTEncoding_Term.mkForall _156_1394))
in (_156_1395, Some ("\\/ interpretation")))
in FStar_SMTEncoding_Term.Assume (_156_1396))
in (_156_1397)::[])))))))))
in (
# 1106 "FStar.SMTEncoding.Encode.fst"
let mk_eq2_interp = (fun eq2 tt -> (
# 1107 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1108 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1109 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1110 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1111 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1112 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1113 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1114 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1115 "FStar.SMTEncoding.Encode.fst"
let valid = (let _156_1404 = (let _156_1403 = (let _156_1402 = (FStar_SMTEncoding_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_156_1402)::[])
in ("Valid", _156_1403))
in (FStar_SMTEncoding_Term.mkApp _156_1404))
in (let _156_1411 = (let _156_1410 = (let _156_1409 = (let _156_1408 = (let _156_1407 = (let _156_1406 = (let _156_1405 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_156_1405, valid))
in (FStar_SMTEncoding_Term.mkIff _156_1406))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _156_1407))
in (FStar_SMTEncoding_Term.mkForall _156_1408))
in (_156_1409, Some ("Eq2 interpretation")))
in FStar_SMTEncoding_Term.Assume (_156_1410))
in (_156_1411)::[])))))))))))
in (
# 1117 "FStar.SMTEncoding.Encode.fst"
let mk_imp_interp = (fun imp tt -> (
# 1118 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1119 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1120 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1121 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1122 "FStar.SMTEncoding.Encode.fst"
let valid = (let _156_1418 = (let _156_1417 = (let _156_1416 = (FStar_SMTEncoding_Term.mkApp (imp, (a)::(b)::[]))
in (_156_1416)::[])
in ("Valid", _156_1417))
in (FStar_SMTEncoding_Term.mkApp _156_1418))
in (
# 1123 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1124 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _156_1425 = (let _156_1424 = (let _156_1423 = (let _156_1422 = (let _156_1421 = (let _156_1420 = (let _156_1419 = (FStar_SMTEncoding_Term.mkImp (valid_a, valid_b))
in (_156_1419, valid))
in (FStar_SMTEncoding_Term.mkIff _156_1420))
in (((valid)::[])::[], (aa)::(bb)::[], _156_1421))
in (FStar_SMTEncoding_Term.mkForall _156_1422))
in (_156_1423, Some ("==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_156_1424))
in (_156_1425)::[])))))))))
in (
# 1126 "FStar.SMTEncoding.Encode.fst"
let mk_iff_interp = (fun iff tt -> (
# 1127 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1128 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1129 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1130 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1131 "FStar.SMTEncoding.Encode.fst"
let valid = (let _156_1432 = (let _156_1431 = (let _156_1430 = (FStar_SMTEncoding_Term.mkApp (iff, (a)::(b)::[]))
in (_156_1430)::[])
in ("Valid", _156_1431))
in (FStar_SMTEncoding_Term.mkApp _156_1432))
in (
# 1132 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1133 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _156_1439 = (let _156_1438 = (let _156_1437 = (let _156_1436 = (let _156_1435 = (let _156_1434 = (let _156_1433 = (FStar_SMTEncoding_Term.mkIff (valid_a, valid_b))
in (_156_1433, valid))
in (FStar_SMTEncoding_Term.mkIff _156_1434))
in (((valid)::[])::[], (aa)::(bb)::[], _156_1435))
in (FStar_SMTEncoding_Term.mkForall _156_1436))
in (_156_1437, Some ("<==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_156_1438))
in (_156_1439)::[])))))))))
in (
# 1135 "FStar.SMTEncoding.Encode.fst"
let mk_forall_interp = (fun for_all tt -> (
# 1136 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1137 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1138 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1139 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1140 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1141 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1142 "FStar.SMTEncoding.Encode.fst"
let valid = (let _156_1446 = (let _156_1445 = (let _156_1444 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_156_1444)::[])
in ("Valid", _156_1445))
in (FStar_SMTEncoding_Term.mkApp _156_1446))
in (
# 1143 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _156_1449 = (let _156_1448 = (let _156_1447 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_156_1447)::[])
in ("Valid", _156_1448))
in (FStar_SMTEncoding_Term.mkApp _156_1449))
in (let _156_1463 = (let _156_1462 = (let _156_1461 = (let _156_1460 = (let _156_1459 = (let _156_1458 = (let _156_1457 = (let _156_1456 = (let _156_1455 = (let _156_1451 = (let _156_1450 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_156_1450)::[])
in (_156_1451)::[])
in (let _156_1454 = (let _156_1453 = (let _156_1452 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_156_1452, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _156_1453))
in (_156_1455, (xx)::[], _156_1454)))
in (FStar_SMTEncoding_Term.mkForall _156_1456))
in (_156_1457, valid))
in (FStar_SMTEncoding_Term.mkIff _156_1458))
in (((valid)::[])::[], (aa)::(bb)::[], _156_1459))
in (FStar_SMTEncoding_Term.mkForall _156_1460))
in (_156_1461, Some ("forall interpretation")))
in FStar_SMTEncoding_Term.Assume (_156_1462))
in (_156_1463)::[]))))))))))
in (
# 1145 "FStar.SMTEncoding.Encode.fst"
let mk_exists_interp = (fun for_all tt -> (
# 1146 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1147 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1148 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1149 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1150 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1151 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1152 "FStar.SMTEncoding.Encode.fst"
let valid = (let _156_1470 = (let _156_1469 = (let _156_1468 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_156_1468)::[])
in ("Valid", _156_1469))
in (FStar_SMTEncoding_Term.mkApp _156_1470))
in (
# 1153 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _156_1473 = (let _156_1472 = (let _156_1471 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_156_1471)::[])
in ("Valid", _156_1472))
in (FStar_SMTEncoding_Term.mkApp _156_1473))
in (let _156_1487 = (let _156_1486 = (let _156_1485 = (let _156_1484 = (let _156_1483 = (let _156_1482 = (let _156_1481 = (let _156_1480 = (let _156_1479 = (let _156_1475 = (let _156_1474 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_156_1474)::[])
in (_156_1475)::[])
in (let _156_1478 = (let _156_1477 = (let _156_1476 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_156_1476, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _156_1477))
in (_156_1479, (xx)::[], _156_1478)))
in (FStar_SMTEncoding_Term.mkExists _156_1480))
in (_156_1481, valid))
in (FStar_SMTEncoding_Term.mkIff _156_1482))
in (((valid)::[])::[], (aa)::(bb)::[], _156_1483))
in (FStar_SMTEncoding_Term.mkForall _156_1484))
in (_156_1485, Some ("exists interpretation")))
in FStar_SMTEncoding_Term.Assume (_156_1486))
in (_156_1487)::[]))))))))))
in (
# 1156 "FStar.SMTEncoding.Encode.fst"
let prims = ((FStar_Syntax_Const.unit_lid, mk_unit))::((FStar_Syntax_Const.bool_lid, mk_bool))::((FStar_Syntax_Const.int_lid, mk_int))::((FStar_Syntax_Const.string_lid, mk_str))::((FStar_Syntax_Const.ref_lid, mk_ref))::((FStar_Syntax_Const.char_lid, mk_int_alias))::((FStar_Syntax_Const.uint8_lid, mk_int_alias))::((FStar_Syntax_Const.false_lid, mk_false_interp))::((FStar_Syntax_Const.and_lid, mk_and_interp))::((FStar_Syntax_Const.or_lid, mk_or_interp))::((FStar_Syntax_Const.eq2_lid, mk_eq2_interp))::((FStar_Syntax_Const.imp_lid, mk_imp_interp))::((FStar_Syntax_Const.iff_lid, mk_iff_interp))::((FStar_Syntax_Const.forall_lid, mk_forall_interp))::((FStar_Syntax_Const.exists_lid, mk_exists_interp))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _77_1878 -> (match (_77_1878) with
| (l, _77_1877) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_77_1881, f) -> begin
(f s tt)
end)))))))))))))))))))))

# 1177 "FStar.SMTEncoding.Encode.fst"
let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1178 "FStar.SMTEncoding.Encode.fst"
let _77_1887 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _156_1630 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _156_1630))
end else begin
()
end
in (
# 1181 "FStar.SMTEncoding.Encode.fst"
let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (
# 1184 "FStar.SMTEncoding.Encode.fst"
let _77_1895 = (encode_sigelt' env se)
in (match (_77_1895) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _156_1633 = (let _156_1632 = (let _156_1631 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_156_1631))
in (_156_1632)::[])
in (_156_1633, e))
end
| _77_1898 -> begin
(let _156_1640 = (let _156_1639 = (let _156_1635 = (let _156_1634 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_156_1634))
in (_156_1635)::g)
in (let _156_1638 = (let _156_1637 = (let _156_1636 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_156_1636))
in (_156_1637)::[])
in (FStar_List.append _156_1639 _156_1638)))
in (_156_1640, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1190 "FStar.SMTEncoding.Encode.fst"
let should_skip = (fun l -> false)
in (
# 1196 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_val = (fun env lid t quals -> (
# 1197 "FStar.SMTEncoding.Encode.fst"
let tt = (whnf env t)
in (
# 1202 "FStar.SMTEncoding.Encode.fst"
let _77_1911 = (encode_free_var env lid t tt quals)
in (match (_77_1911) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _156_1654 = (let _156_1653 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _156_1653))
in (_156_1654, env))
end else begin
(decls, env)
end
end))))
in (
# 1208 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _77_1918 lb -> (match (_77_1918) with
| (decls, env) -> begin
(
# 1210 "FStar.SMTEncoding.Encode.fst"
let _77_1922 = (let _156_1663 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _156_1663 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_77_1922) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _77_1940, _77_1942, _77_1944, _77_1946) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(
# 1222 "FStar.SMTEncoding.Encode.fst"
let _77_1952 = (new_term_constant_and_tok_from_lid env lid)
in (match (_77_1952) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _77_1955, t, quals, _77_1959) -> begin
if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _77_12 -> (match (_77_12) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) -> begin
true
end
| _77_1971 -> begin
false
end)))) || env.tcenv.FStar_TypeChecker_Env.is_iface) then begin
(
# 1227 "FStar.SMTEncoding.Encode.fst"
let _77_1974 = (encode_top_level_val env lid t quals)
in (match (_77_1974) with
| (decls, env) -> begin
(
# 1228 "FStar.SMTEncoding.Encode.fst"
let tname = lid.FStar_Ident.str
in (
# 1229 "FStar.SMTEncoding.Encode.fst"
let tsym = (FStar_SMTEncoding_Term.mkFreeV (tname, FStar_SMTEncoding_Term.Term_sort))
in (let _156_1666 = (let _156_1665 = (primitive_type_axioms lid tname tsym)
in (FStar_List.append decls _156_1665))
in (_156_1666, env))))
end))
end else begin
([], env)
end
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _77_1980, _77_1982) -> begin
(
# 1236 "FStar.SMTEncoding.Encode.fst"
let _77_1987 = (encode_formula f env)
in (match (_77_1987) with
| (f, decls) -> begin
(
# 1237 "FStar.SMTEncoding.Encode.fst"
let g = (let _156_1671 = (let _156_1670 = (let _156_1669 = (let _156_1668 = (let _156_1667 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _156_1667))
in Some (_156_1668))
in (f, _156_1669))
in FStar_SMTEncoding_Term.Assume (_156_1670))
in (_156_1671)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _77_1992, _77_1994) when (FStar_All.pipe_right (Prims.snd lbs) (FStar_Util.for_some (fun lb -> (let _156_1673 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (should_skip _156_1673))))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((_77_1999, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _77_2007; FStar_Syntax_Syntax.lbtyp = _77_2005; FStar_Syntax_Syntax.lbeff = _77_2003; FStar_Syntax_Syntax.lbdef = _77_2001}::[]), _77_2014, _77_2016, _77_2018) when (FStar_Ident.lid_equals b2t FStar_Syntax_Const.b2t_lid) -> begin
(
# 1244 "FStar.SMTEncoding.Encode.fst"
let _77_2024 = (new_term_constant_and_tok_from_lid env b2t)
in (match (_77_2024) with
| (tname, ttok, env) -> begin
(
# 1245 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1246 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1247 "FStar.SMTEncoding.Encode.fst"
let valid_b2t_x = (let _156_1676 = (let _156_1675 = (let _156_1674 = (FStar_SMTEncoding_Term.mkApp ("Prims.b2t", (x)::[]))
in (_156_1674)::[])
in ("Valid", _156_1675))
in (FStar_SMTEncoding_Term.mkApp _156_1676))
in (
# 1248 "FStar.SMTEncoding.Encode.fst"
let decls = (let _156_1684 = (let _156_1683 = (let _156_1682 = (let _156_1681 = (let _156_1680 = (let _156_1679 = (let _156_1678 = (let _156_1677 = (FStar_SMTEncoding_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _156_1677))
in (FStar_SMTEncoding_Term.mkEq _156_1678))
in (((valid_b2t_x)::[])::[], (xx)::[], _156_1679))
in (FStar_SMTEncoding_Term.mkForall _156_1680))
in (_156_1681, Some ("b2t def")))
in FStar_SMTEncoding_Term.Assume (_156_1682))
in (_156_1683)::[])
in (FStar_SMTEncoding_Term.DeclFun ((tname, (FStar_SMTEncoding_Term.Term_sort)::[], FStar_SMTEncoding_Term.Term_sort, None)))::_156_1684)
in (decls, env)))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_77_2030, _77_2032, _77_2034, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _77_13 -> (match (_77_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _77_2044 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _77_2050, _77_2052, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _77_14 -> (match (_77_14) with
| FStar_Syntax_Syntax.Projector (_77_2058) -> begin
true
end
| _77_2061 -> begin
false
end)))) -> begin
(
# 1262 "FStar.SMTEncoding.Encode.fst"
let l = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (match ((try_lookup_free_var env l)) with
| Some (_77_2064) -> begin
([], env)
end
| None -> begin
(
# 1267 "FStar.SMTEncoding.Encode.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((l, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, (FStar_Ident.range_of_lid l)))
in (encode_sigelt env se))
end))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _77_2072, _77_2074, quals) -> begin
(
# 1273 "FStar.SMTEncoding.Encode.fst"
let eta_expand = (fun binders formals body t -> (
# 1274 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1275 "FStar.SMTEncoding.Encode.fst"
let _77_2086 = (FStar_Util.first_N nbinders formals)
in (match (_77_2086) with
| (formals, extra_formals) -> begin
(
# 1276 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _77_2090 _77_2094 -> (match ((_77_2090, _77_2094)) with
| ((formal, _77_2089), (binder, _77_2093)) -> begin
(let _156_1698 = (let _156_1697 = (FStar_Syntax_Syntax.bv_to_name binder)
in (formal, _156_1697))
in FStar_Syntax_Syntax.NT (_156_1698))
end)) formals binders)
in (
# 1277 "FStar.SMTEncoding.Encode.fst"
let extra_formals = (let _156_1702 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _77_2098 -> (match (_77_2098) with
| (x, i) -> begin
(let _156_1701 = (
# 1277 "FStar.SMTEncoding.Encode.fst"
let _77_2099 = x
in (let _156_1700 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _77_2099.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _77_2099.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _156_1700}))
in (_156_1701, i))
end))))
in (FStar_All.pipe_right _156_1702 FStar_Syntax_Util.name_binders))
in (
# 1278 "FStar.SMTEncoding.Encode.fst"
let body = (let _156_1709 = (FStar_Syntax_Subst.compress body)
in (let _156_1708 = (let _156_1703 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _156_1703))
in (let _156_1707 = (let _156_1706 = (let _156_1705 = (FStar_Syntax_Subst.subst subst t)
in _156_1705.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _156_1704 -> Some (_156_1704)) _156_1706))
in (FStar_Syntax_Syntax.extend_app_n _156_1709 _156_1708 _156_1707 body.FStar_Syntax_Syntax.pos))))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (
# 1281 "FStar.SMTEncoding.Encode.fst"
let rec destruct_bound_function = (fun flid t_norm e -> (match ((let _156_1716 = (FStar_Syntax_Util.unascribe e)
in _156_1716.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(
# 1284 "FStar.SMTEncoding.Encode.fst"
let _77_2115 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_77_2115) with
| (binders, body, opening) -> begin
(match ((let _156_1717 = (FStar_Syntax_Subst.compress t_norm)
in _156_1717.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1287 "FStar.SMTEncoding.Encode.fst"
let _77_2122 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_77_2122) with
| (formals, c) -> begin
(
# 1288 "FStar.SMTEncoding.Encode.fst"
let nformals = (FStar_List.length formals)
in (
# 1289 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1290 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c)) then begin
(
# 1292 "FStar.SMTEncoding.Encode.fst"
let lopt = (subst_lcomp_opt opening lopt)
in (
# 1293 "FStar.SMTEncoding.Encode.fst"
let _77_2129 = (FStar_Util.first_N nformals binders)
in (match (_77_2129) with
| (bs0, rest) -> begin
(
# 1294 "FStar.SMTEncoding.Encode.fst"
let c = (
# 1295 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _77_2133 _77_2137 -> (match ((_77_2133, _77_2137)) with
| ((b, _77_2132), (x, _77_2136)) -> begin
(let _156_1721 = (let _156_1720 = (FStar_Syntax_Syntax.bv_to_name x)
in (b, _156_1720))
in FStar_Syntax_Syntax.NT (_156_1721))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (
# 1297 "FStar.SMTEncoding.Encode.fst"
let body = (FStar_Syntax_Util.abs rest body lopt)
in (bs0, body, bs0, (FStar_Syntax_Util.comp_result c))))
end)))
end else begin
if (nformals > nbinders) then begin
(
# 1300 "FStar.SMTEncoding.Encode.fst"
let _77_2143 = (eta_expand binders formals body tres)
in (match (_77_2143) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end))
end
| _77_2145 -> begin
(let _156_1724 = (let _156_1723 = (FStar_Syntax_Print.term_to_string e)
in (let _156_1722 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _156_1723 _156_1722)))
in (FStar_All.failwith _156_1724))
end)
end))
end
| _77_2147 -> begin
(match ((let _156_1725 = (FStar_Syntax_Subst.compress t_norm)
in _156_1725.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1310 "FStar.SMTEncoding.Encode.fst"
let _77_2154 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_77_2154) with
| (formals, c) -> begin
(
# 1311 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in (
# 1312 "FStar.SMTEncoding.Encode.fst"
let _77_2158 = (eta_expand [] formals e tres)
in (match (_77_2158) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end))
end
| _77_2160 -> begin
([], e, [], t_norm)
end)
end))
in (FStar_All.try_with (fun _77_2162 -> (match (()) with
| () -> begin
if (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(
# 1320 "FStar.SMTEncoding.Encode.fst"
let _77_2188 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _77_2175 lb -> (match (_77_2175) with
| (toks, typs, decls, env) -> begin
(
# 1322 "FStar.SMTEncoding.Encode.fst"
let _77_2177 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (
# 1323 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 1324 "FStar.SMTEncoding.Encode.fst"
let _77_2183 = (let _156_1730 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _156_1730 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_77_2183) with
| (tok, decl, env) -> begin
(let _156_1733 = (let _156_1732 = (let _156_1731 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_156_1731, tok))
in (_156_1732)::toks)
in (_156_1733, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_77_2188) with
| (toks, typs, decls, env) -> begin
(
# 1326 "FStar.SMTEncoding.Encode.fst"
let toks = (FStar_List.rev toks)
in (
# 1327 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (
# 1328 "FStar.SMTEncoding.Encode.fst"
let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _77_15 -> (match (_77_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _77_2195 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _156_1736 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _156_1736)))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Syntax_Syntax.lbname = _77_2205; FStar_Syntax_Syntax.lbunivs = _77_2203; FStar_Syntax_Syntax.lbtyp = _77_2201; FStar_Syntax_Syntax.lbeff = _77_2199; FStar_Syntax_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(
# 1335 "FStar.SMTEncoding.Encode.fst"
let e = (FStar_Syntax_Subst.compress e)
in (
# 1336 "FStar.SMTEncoding.Encode.fst"
let _77_2224 = (destruct_bound_function flid t_norm e)
in (match (_77_2224) with
| (binders, body, _77_2221, _77_2223) -> begin
(
# 1337 "FStar.SMTEncoding.Encode.fst"
let _77_2231 = (encode_binders None binders env)
in (match (_77_2231) with
| (vars, guards, env', binder_decls, _77_2230) -> begin
(
# 1338 "FStar.SMTEncoding.Encode.fst"
let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
end
| _77_2234 -> begin
(let _156_1738 = (let _156_1737 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (f, _156_1737))
in (FStar_SMTEncoding_Term.mkApp _156_1738))
end)
in (
# 1339 "FStar.SMTEncoding.Encode.fst"
let _77_2240 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _156_1740 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _156_1739 = (encode_formula body env')
in (_156_1740, _156_1739)))
end else begin
(let _156_1741 = (encode_term body env')
in (app, _156_1741))
end
in (match (_77_2240) with
| (app, (body, decls2)) -> begin
(
# 1343 "FStar.SMTEncoding.Encode.fst"
let eqn = (let _156_1750 = (let _156_1749 = (let _156_1746 = (let _156_1745 = (let _156_1744 = (let _156_1743 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _156_1742 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_156_1743, _156_1742)))
in (FStar_SMTEncoding_Term.mkImp _156_1744))
in (((app)::[])::[], vars, _156_1745))
in (FStar_SMTEncoding_Term.mkForall _156_1746))
in (let _156_1748 = (let _156_1747 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_156_1747))
in (_156_1749, _156_1748)))
in FStar_SMTEncoding_Term.Assume (_156_1750))
in ((FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end)))
end
| _77_2243 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 1347 "FStar.SMTEncoding.Encode.fst"
let fuel = (let _156_1751 = (varops.fresh "fuel")
in (_156_1751, FStar_SMTEncoding_Term.Fuel_sort))
in (
# 1348 "FStar.SMTEncoding.Encode.fst"
let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (
# 1349 "FStar.SMTEncoding.Encode.fst"
let env0 = env
in (
# 1350 "FStar.SMTEncoding.Encode.fst"
let _77_2260 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _77_2249 _77_2254 -> (match ((_77_2249, _77_2254)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(
# 1351 "FStar.SMTEncoding.Encode.fst"
let g = (varops.new_fvar flid)
in (
# 1352 "FStar.SMTEncoding.Encode.fst"
let gtok = (varops.new_fvar flid)
in (
# 1353 "FStar.SMTEncoding.Encode.fst"
let env = (let _156_1756 = (let _156_1755 = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _156_1754 -> Some (_156_1754)) _156_1755))
in (push_free_var env flid gtok _156_1756))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_77_2260) with
| (gtoks, env) -> begin
(
# 1355 "FStar.SMTEncoding.Encode.fst"
let gtoks = (FStar_List.rev gtoks)
in (
# 1356 "FStar.SMTEncoding.Encode.fst"
let encode_one_binding = (fun env0 _77_2269 t_norm _77_2280 -> (match ((_77_2269, _77_2280)) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _77_2279; FStar_Syntax_Syntax.lbunivs = _77_2277; FStar_Syntax_Syntax.lbtyp = _77_2275; FStar_Syntax_Syntax.lbeff = _77_2273; FStar_Syntax_Syntax.lbdef = e}) -> begin
(
# 1357 "FStar.SMTEncoding.Encode.fst"
let _77_2285 = (destruct_bound_function flid t_norm e)
in (match (_77_2285) with
| (binders, body, formals, tres) -> begin
(
# 1358 "FStar.SMTEncoding.Encode.fst"
let _77_2292 = (encode_binders None binders env)
in (match (_77_2292) with
| (vars, guards, env', binder_decls, _77_2291) -> begin
(
# 1359 "FStar.SMTEncoding.Encode.fst"
let decl_g = (let _156_1767 = (let _156_1766 = (let _156_1765 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_156_1765)
in (g, _156_1766, FStar_SMTEncoding_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_SMTEncoding_Term.DeclFun (_156_1767))
in (
# 1360 "FStar.SMTEncoding.Encode.fst"
let env0 = (push_zfuel_name env0 flid g)
in (
# 1361 "FStar.SMTEncoding.Encode.fst"
let decl_g_tok = FStar_SMTEncoding_Term.DeclFun ((gtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (
# 1362 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1363 "FStar.SMTEncoding.Encode.fst"
let app = (FStar_SMTEncoding_Term.mkApp (f, vars_tm))
in (
# 1364 "FStar.SMTEncoding.Encode.fst"
let gsapp = (let _156_1770 = (let _156_1769 = (let _156_1768 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_156_1768)::vars_tm)
in (g, _156_1769))
in (FStar_SMTEncoding_Term.mkApp _156_1770))
in (
# 1365 "FStar.SMTEncoding.Encode.fst"
let gmax = (let _156_1773 = (let _156_1772 = (let _156_1771 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (_156_1771)::vars_tm)
in (g, _156_1772))
in (FStar_SMTEncoding_Term.mkApp _156_1773))
in (
# 1366 "FStar.SMTEncoding.Encode.fst"
let _77_2302 = (encode_term body env')
in (match (_77_2302) with
| (body_tm, decls2) -> begin
(
# 1367 "FStar.SMTEncoding.Encode.fst"
let eqn_g = (let _156_1782 = (let _156_1781 = (let _156_1778 = (let _156_1777 = (let _156_1776 = (let _156_1775 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _156_1774 = (FStar_SMTEncoding_Term.mkEq (gsapp, body_tm))
in (_156_1775, _156_1774)))
in (FStar_SMTEncoding_Term.mkImp _156_1776))
in (((gsapp)::[])::[], (fuel)::vars, _156_1777))
in (FStar_SMTEncoding_Term.mkForall _156_1778))
in (let _156_1780 = (let _156_1779 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_156_1779))
in (_156_1781, _156_1780)))
in FStar_SMTEncoding_Term.Assume (_156_1782))
in (
# 1369 "FStar.SMTEncoding.Encode.fst"
let eqn_f = (let _156_1786 = (let _156_1785 = (let _156_1784 = (let _156_1783 = (FStar_SMTEncoding_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _156_1783))
in (FStar_SMTEncoding_Term.mkForall _156_1784))
in (_156_1785, Some ("Correspondence of recursive function to instrumented version")))
in FStar_SMTEncoding_Term.Assume (_156_1786))
in (
# 1371 "FStar.SMTEncoding.Encode.fst"
let eqn_g' = (let _156_1795 = (let _156_1794 = (let _156_1793 = (let _156_1792 = (let _156_1791 = (let _156_1790 = (let _156_1789 = (let _156_1788 = (let _156_1787 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_156_1787)::vars_tm)
in (g, _156_1788))
in (FStar_SMTEncoding_Term.mkApp _156_1789))
in (gsapp, _156_1790))
in (FStar_SMTEncoding_Term.mkEq _156_1791))
in (((gsapp)::[])::[], (fuel)::vars, _156_1792))
in (FStar_SMTEncoding_Term.mkForall _156_1793))
in (_156_1794, Some ("Fuel irrelevance")))
in FStar_SMTEncoding_Term.Assume (_156_1795))
in (
# 1373 "FStar.SMTEncoding.Encode.fst"
let _77_2325 = (
# 1374 "FStar.SMTEncoding.Encode.fst"
let _77_2312 = (encode_binders None formals env0)
in (match (_77_2312) with
| (vars, v_guards, env, binder_decls, _77_2311) -> begin
(
# 1375 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1376 "FStar.SMTEncoding.Encode.fst"
let gapp = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::vars_tm))
in (
# 1377 "FStar.SMTEncoding.Encode.fst"
let tok_corr = (
# 1378 "FStar.SMTEncoding.Encode.fst"
let tok_app = (let _156_1796 = (FStar_SMTEncoding_Term.mkFreeV (gtok, FStar_SMTEncoding_Term.Term_sort))
in (mk_Apply _156_1796 ((fuel)::vars)))
in (let _156_1800 = (let _156_1799 = (let _156_1798 = (let _156_1797 = (FStar_SMTEncoding_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _156_1797))
in (FStar_SMTEncoding_Term.mkForall _156_1798))
in (_156_1799, Some ("Fuel token correspondence")))
in FStar_SMTEncoding_Term.Assume (_156_1800)))
in (
# 1381 "FStar.SMTEncoding.Encode.fst"
let _77_2322 = (
# 1382 "FStar.SMTEncoding.Encode.fst"
let _77_2319 = (encode_term_pred None tres env gapp)
in (match (_77_2319) with
| (g_typing, d3) -> begin
(let _156_1808 = (let _156_1807 = (let _156_1806 = (let _156_1805 = (let _156_1804 = (let _156_1803 = (let _156_1802 = (let _156_1801 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in (_156_1801, g_typing))
in (FStar_SMTEncoding_Term.mkImp _156_1802))
in (((gapp)::[])::[], (fuel)::vars, _156_1803))
in (FStar_SMTEncoding_Term.mkForall _156_1804))
in (_156_1805, None))
in FStar_SMTEncoding_Term.Assume (_156_1806))
in (_156_1807)::[])
in (d3, _156_1808))
end))
in (match (_77_2322) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_77_2325) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (
# 1386 "FStar.SMTEncoding.Encode.fst"
let _77_2341 = (let _156_1811 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _77_2329 _77_2333 -> (match ((_77_2329, _77_2333)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(
# 1387 "FStar.SMTEncoding.Encode.fst"
let _77_2337 = (encode_one_binding env0 gtok ty bs)
in (match (_77_2337) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _156_1811))
in (match (_77_2341) with
| (decls, eqns, env0) -> begin
(
# 1389 "FStar.SMTEncoding.Encode.fst"
let _77_2350 = (let _156_1813 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _156_1813 (FStar_List.partition (fun _77_16 -> (match (_77_16) with
| FStar_SMTEncoding_Term.DeclFun (_77_2344) -> begin
true
end
| _77_2347 -> begin
false
end)))))
in (match (_77_2350) with
| (prefix_decls, rest) -> begin
(
# 1392 "FStar.SMTEncoding.Encode.fst"
let eqns = (FStar_List.rev eqns)
in ((FStar_List.append (FStar_List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end
end)))
end))
end
end)) (fun _77_2161 -> (match (_77_2161) with
| Let_rec_unencodeable -> begin
(
# 1395 "FStar.SMTEncoding.Encode.fst"
let msg = (let _156_1816 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _156_1816 (FStar_String.concat " and ")))
in (
# 1396 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _77_2354, _77_2356, _77_2358) -> begin
(
# 1401 "FStar.SMTEncoding.Encode.fst"
let _77_2363 = (encode_signature env ses)
in (match (_77_2363) with
| (g, env) -> begin
(
# 1402 "FStar.SMTEncoding.Encode.fst"
let _77_2375 = (FStar_All.pipe_right g (FStar_List.partition (fun _77_17 -> (match (_77_17) with
| FStar_SMTEncoding_Term.Assume (_77_2366, Some ("inversion axiom")) -> begin
false
end
| _77_2372 -> begin
true
end))))
in (match (_77_2375) with
| (g', inversions) -> begin
(
# 1405 "FStar.SMTEncoding.Encode.fst"
let _77_2384 = (FStar_All.pipe_right g' (FStar_List.partition (fun _77_18 -> (match (_77_18) with
| FStar_SMTEncoding_Term.DeclFun (_77_2378) -> begin
true
end
| _77_2381 -> begin
false
end))))
in (match (_77_2384) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _77_2387, tps, k, _77_2391, datas, quals, _77_2395) -> begin
(
# 1411 "FStar.SMTEncoding.Encode.fst"
let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _77_19 -> (match (_77_19) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _77_2402 -> begin
false
end))))
in (
# 1412 "FStar.SMTEncoding.Encode.fst"
let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(
# 1414 "FStar.SMTEncoding.Encode.fst"
let _77_2412 = c
in (match (_77_2412) with
| (name, args, _77_2409, _77_2411) -> begin
(let _156_1824 = (let _156_1823 = (let _156_1822 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _156_1822, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_156_1823))
in (_156_1824)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (
# 1418 "FStar.SMTEncoding.Encode.fst"
let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _156_1830 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _156_1830 FStar_Option.isNone))))) then begin
[]
end else begin
(
# 1422 "FStar.SMTEncoding.Encode.fst"
let _77_2419 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_77_2419) with
| (xxsym, xx) -> begin
(
# 1423 "FStar.SMTEncoding.Encode.fst"
let _77_2455 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _77_2422 l -> (match (_77_2422) with
| (out, decls) -> begin
(
# 1424 "FStar.SMTEncoding.Encode.fst"
let _77_2427 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_77_2427) with
| (_77_2425, data_t) -> begin
(
# 1425 "FStar.SMTEncoding.Encode.fst"
let _77_2430 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_77_2430) with
| (args, res) -> begin
(
# 1426 "FStar.SMTEncoding.Encode.fst"
let indices = (match ((let _156_1833 = (FStar_Syntax_Subst.compress res)
in _156_1833.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_77_2432, indices) -> begin
indices
end
| _77_2437 -> begin
[]
end)
in (
# 1429 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _77_2443 -> (match (_77_2443) with
| (x, _77_2442) -> begin
(let _156_1838 = (let _156_1837 = (let _156_1836 = (mk_term_projector_name l x)
in (_156_1836, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _156_1837))
in (push_term_var env x _156_1838))
end)) env))
in (
# 1432 "FStar.SMTEncoding.Encode.fst"
let _77_2447 = (encode_args indices env)
in (match (_77_2447) with
| (indices, decls') -> begin
(
# 1433 "FStar.SMTEncoding.Encode.fst"
let _77_2448 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (
# 1435 "FStar.SMTEncoding.Encode.fst"
let eqs = (let _156_1843 = (FStar_List.map2 (fun v a -> (let _156_1842 = (let _156_1841 = (FStar_SMTEncoding_Term.mkFreeV v)
in (_156_1841, a))
in (FStar_SMTEncoding_Term.mkEq _156_1842))) vars indices)
in (FStar_All.pipe_right _156_1843 FStar_SMTEncoding_Term.mk_and_l))
in (let _156_1848 = (let _156_1847 = (let _156_1846 = (let _156_1845 = (let _156_1844 = (mk_data_tester env l xx)
in (_156_1844, eqs))
in (FStar_SMTEncoding_Term.mkAnd _156_1845))
in (out, _156_1846))
in (FStar_SMTEncoding_Term.mkOr _156_1847))
in (_156_1848, (FStar_List.append decls decls')))))
end))))
end))
end))
end)) (FStar_SMTEncoding_Term.mkFalse, [])))
in (match (_77_2455) with
| (data_ax, decls) -> begin
(
# 1437 "FStar.SMTEncoding.Encode.fst"
let _77_2458 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_77_2458) with
| (ffsym, ff) -> begin
(
# 1438 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (let _156_1849 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _156_1849 xx tapp))
in (let _156_1856 = (let _156_1855 = (let _156_1854 = (let _156_1853 = (let _156_1852 = (let _156_1851 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _156_1850 = (FStar_SMTEncoding_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _156_1851, _156_1850)))
in (FStar_SMTEncoding_Term.mkForall _156_1852))
in (_156_1853, Some ("inversion axiom")))
in FStar_SMTEncoding_Term.Assume (_156_1854))
in (_156_1855)::[])
in (FStar_List.append decls _156_1856)))
end))
end))
end))
end)
in (
# 1442 "FStar.SMTEncoding.Encode.fst"
let _77_2468 = (match ((let _156_1857 = (FStar_Syntax_Subst.compress k)
in _156_1857.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
((FStar_List.append tps formals), (FStar_Syntax_Util.comp_result kres))
end
| _77_2465 -> begin
(tps, k)
end)
in (match (_77_2468) with
| (formals, res) -> begin
(
# 1448 "FStar.SMTEncoding.Encode.fst"
let _77_2471 = (FStar_Syntax_Subst.open_term formals res)
in (match (_77_2471) with
| (formals, res) -> begin
(
# 1449 "FStar.SMTEncoding.Encode.fst"
let _77_2478 = (encode_binders None formals env)
in (match (_77_2478) with
| (vars, guards, env', binder_decls, _77_2477) -> begin
(
# 1451 "FStar.SMTEncoding.Encode.fst"
let pretype_axioms = (fun tapp vars -> (
# 1452 "FStar.SMTEncoding.Encode.fst"
let _77_2484 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_77_2484) with
| (xxsym, xx) -> begin
(
# 1453 "FStar.SMTEncoding.Encode.fst"
let _77_2487 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_77_2487) with
| (ffsym, ff) -> begin
(
# 1454 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _156_1870 = (let _156_1869 = (let _156_1868 = (let _156_1867 = (let _156_1866 = (let _156_1865 = (let _156_1864 = (let _156_1863 = (let _156_1862 = (FStar_SMTEncoding_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _156_1862))
in (FStar_SMTEncoding_Term.mkEq _156_1863))
in (xx_has_type, _156_1864))
in (FStar_SMTEncoding_Term.mkImp _156_1865))
in (((xx_has_type)::[])::[], ((xxsym, FStar_SMTEncoding_Term.Term_sort))::((ffsym, FStar_SMTEncoding_Term.Fuel_sort))::vars, _156_1866))
in (FStar_SMTEncoding_Term.mkForall _156_1867))
in (_156_1868, Some ("pretyping")))
in FStar_SMTEncoding_Term.Assume (_156_1869))
in (_156_1870)::[]))
end))
end)))
in (
# 1458 "FStar.SMTEncoding.Encode.fst"
let _77_2492 = (new_term_constant_and_tok_from_lid env t)
in (match (_77_2492) with
| (tname, ttok, env) -> begin
(
# 1459 "FStar.SMTEncoding.Encode.fst"
let ttok_tm = (FStar_SMTEncoding_Term.mkApp (ttok, []))
in (
# 1460 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1461 "FStar.SMTEncoding.Encode.fst"
let tapp = (let _156_1872 = (let _156_1871 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (tname, _156_1871))
in (FStar_SMTEncoding_Term.mkApp _156_1872))
in (
# 1462 "FStar.SMTEncoding.Encode.fst"
let _77_2513 = (
# 1463 "FStar.SMTEncoding.Encode.fst"
let tname_decl = (let _156_1876 = (let _156_1875 = (FStar_All.pipe_right vars (FStar_List.map (fun _77_2498 -> (match (_77_2498) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _156_1874 = (varops.next_id ())
in (tname, _156_1875, FStar_SMTEncoding_Term.Term_sort, _156_1874)))
in (constructor_or_logic_type_decl _156_1876))
in (
# 1464 "FStar.SMTEncoding.Encode.fst"
let _77_2510 = (match (vars) with
| [] -> begin
(let _156_1880 = (let _156_1879 = (let _156_1878 = (FStar_SMTEncoding_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _156_1877 -> Some (_156_1877)) _156_1878))
in (push_free_var env t tname _156_1879))
in ([], _156_1880))
end
| _77_2502 -> begin
(
# 1467 "FStar.SMTEncoding.Encode.fst"
let ttok_decl = FStar_SMTEncoding_Term.DeclFun ((ttok, [], FStar_SMTEncoding_Term.Term_sort, Some ("token")))
in (
# 1468 "FStar.SMTEncoding.Encode.fst"
let ttok_fresh = (let _156_1881 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ttok, FStar_SMTEncoding_Term.Term_sort) _156_1881))
in (
# 1469 "FStar.SMTEncoding.Encode.fst"
let ttok_app = (mk_Apply ttok_tm vars)
in (
# 1470 "FStar.SMTEncoding.Encode.fst"
let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (
# 1473 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _156_1885 = (let _156_1884 = (let _156_1883 = (let _156_1882 = (FStar_SMTEncoding_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _156_1882))
in (FStar_SMTEncoding_Term.mkForall' _156_1883))
in (_156_1884, Some ("name-token correspondence")))
in FStar_SMTEncoding_Term.Assume (_156_1885))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_77_2510) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_77_2513) with
| (decls, env) -> begin
(
# 1476 "FStar.SMTEncoding.Encode.fst"
let kindingAx = (
# 1477 "FStar.SMTEncoding.Encode.fst"
let _77_2516 = (encode_term_pred None res env' tapp)
in (match (_77_2516) with
| (k, decls) -> begin
(
# 1478 "FStar.SMTEncoding.Encode.fst"
let karr = if ((FStar_List.length formals) > 0) then begin
(let _156_1889 = (let _156_1888 = (let _156_1887 = (let _156_1886 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _156_1886))
in (_156_1887, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_156_1888))
in (_156_1889)::[])
end else begin
[]
end
in (let _156_1895 = (let _156_1894 = (let _156_1893 = (let _156_1892 = (let _156_1891 = (let _156_1890 = (FStar_SMTEncoding_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _156_1890))
in (FStar_SMTEncoding_Term.mkForall _156_1891))
in (_156_1892, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_156_1893))
in (_156_1894)::[])
in (FStar_List.append (FStar_List.append decls karr) _156_1895)))
end))
in (
# 1483 "FStar.SMTEncoding.Encode.fst"
let aux = (let _156_1898 = (let _156_1896 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _156_1896))
in (let _156_1897 = (pretype_axioms tapp vars)
in (FStar_List.append _156_1898 _156_1897)))
in (
# 1488 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end)))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _77_2523, _77_2525, _77_2527, _77_2529, _77_2531, _77_2533, _77_2535) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_datacon (d, _77_2540, t, _77_2543, n_tps, quals, _77_2547, drange) -> begin
(
# 1496 "FStar.SMTEncoding.Encode.fst"
let _77_2554 = (new_term_constant_and_tok_from_lid env d)
in (match (_77_2554) with
| (ddconstrsym, ddtok, env) -> begin
(
# 1497 "FStar.SMTEncoding.Encode.fst"
let ddtok_tm = (FStar_SMTEncoding_Term.mkApp (ddtok, []))
in (
# 1498 "FStar.SMTEncoding.Encode.fst"
let _77_2558 = (FStar_Syntax_Util.arrow_formals t)
in (match (_77_2558) with
| (formals, t_res) -> begin
(
# 1499 "FStar.SMTEncoding.Encode.fst"
let _77_2561 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_77_2561) with
| (fuel_var, fuel_tm) -> begin
(
# 1500 "FStar.SMTEncoding.Encode.fst"
let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (
# 1501 "FStar.SMTEncoding.Encode.fst"
let _77_2568 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_77_2568) with
| (vars, guards, env', binder_decls, names) -> begin
(
# 1502 "FStar.SMTEncoding.Encode.fst"
let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _156_1900 = (mk_term_projector_name d x)
in (_156_1900, FStar_SMTEncoding_Term.Term_sort)))))
in (
# 1503 "FStar.SMTEncoding.Encode.fst"
let datacons = (let _156_1902 = (let _156_1901 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_SMTEncoding_Term.Term_sort, _156_1901))
in (FStar_All.pipe_right _156_1902 FStar_SMTEncoding_Term.constructor_to_decl))
in (
# 1504 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply ddtok_tm vars)
in (
# 1505 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1506 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1507 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1509 "FStar.SMTEncoding.Encode.fst"
let _77_2578 = (encode_term_pred None t env ddtok_tm)
in (match (_77_2578) with
| (tok_typing, decls3) -> begin
(
# 1511 "FStar.SMTEncoding.Encode.fst"
let _77_2585 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_77_2585) with
| (vars', guards', env'', decls_formals, _77_2584) -> begin
(
# 1512 "FStar.SMTEncoding.Encode.fst"
let _77_2590 = (
# 1513 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (
# 1514 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_77_2590) with
| (ty_pred', decls_pred) -> begin
(
# 1516 "FStar.SMTEncoding.Encode.fst"
let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (
# 1517 "FStar.SMTEncoding.Encode.fst"
let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _77_2594 -> begin
(let _156_1904 = (let _156_1903 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ddtok, FStar_SMTEncoding_Term.Term_sort) _156_1903))
in (_156_1904)::[])
end)
in (
# 1521 "FStar.SMTEncoding.Encode.fst"
let encode_elim = (fun _77_2597 -> (match (()) with
| () -> begin
(
# 1522 "FStar.SMTEncoding.Encode.fst"
let _77_2600 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_77_2600) with
| (head, args) -> begin
(match ((let _156_1907 = (FStar_Syntax_Subst.compress head)
in _156_1907.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv, _)) -> begin
(
# 1526 "FStar.SMTEncoding.Encode.fst"
let encoded_head = (lookup_free_var_name env' fv)
in (
# 1527 "FStar.SMTEncoding.Encode.fst"
let _77_2624 = (encode_args args env')
in (match (_77_2624) with
| (encoded_args, arg_decls) -> begin
(
# 1528 "FStar.SMTEncoding.Encode.fst"
let _77_2639 = (FStar_List.fold_left (fun _77_2628 arg -> (match (_77_2628) with
| (env, arg_vars, eqns) -> begin
(
# 1529 "FStar.SMTEncoding.Encode.fst"
let _77_2634 = (let _156_1910 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _156_1910))
in (match (_77_2634) with
| (_77_2631, xv, env) -> begin
(let _156_1912 = (let _156_1911 = (FStar_SMTEncoding_Term.mkEq (arg, xv))
in (_156_1911)::eqns)
in (env, (xv)::arg_vars, _156_1912))
end))
end)) (env', [], []) encoded_args)
in (match (_77_2639) with
| (_77_2636, arg_vars, eqns) -> begin
(
# 1531 "FStar.SMTEncoding.Encode.fst"
let arg_vars = (FStar_List.rev arg_vars)
in (
# 1532 "FStar.SMTEncoding.Encode.fst"
let ty = (FStar_SMTEncoding_Term.mkApp (encoded_head, arg_vars))
in (
# 1533 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1534 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1535 "FStar.SMTEncoding.Encode.fst"
let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (
# 1536 "FStar.SMTEncoding.Encode.fst"
let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (
# 1537 "FStar.SMTEncoding.Encode.fst"
let typing_inversion = (let _156_1919 = (let _156_1918 = (let _156_1917 = (let _156_1916 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _156_1915 = (let _156_1914 = (let _156_1913 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _156_1913))
in (FStar_SMTEncoding_Term.mkImp _156_1914))
in (((ty_pred)::[])::[], _156_1916, _156_1915)))
in (FStar_SMTEncoding_Term.mkForall _156_1917))
in (_156_1918, Some ("data constructor typing elim")))
in FStar_SMTEncoding_Term.Assume (_156_1919))
in (
# 1542 "FStar.SMTEncoding.Encode.fst"
let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(
# 1544 "FStar.SMTEncoding.Encode.fst"
let x = (let _156_1920 = (varops.fresh "x")
in (_156_1920, FStar_SMTEncoding_Term.Term_sort))
in (
# 1545 "FStar.SMTEncoding.Encode.fst"
let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _156_1930 = (let _156_1929 = (let _156_1928 = (let _156_1927 = (let _156_1922 = (let _156_1921 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_156_1921)::[])
in (_156_1922)::[])
in (let _156_1926 = (let _156_1925 = (let _156_1924 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _156_1923 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_156_1924, _156_1923)))
in (FStar_SMTEncoding_Term.mkImp _156_1925))
in (_156_1927, (x)::[], _156_1926)))
in (FStar_SMTEncoding_Term.mkForall _156_1928))
in (_156_1929, Some ("lextop is top")))
in FStar_SMTEncoding_Term.Assume (_156_1930))))
end else begin
(
# 1548 "FStar.SMTEncoding.Encode.fst"
let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _156_1933 = (let _156_1932 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _156_1932 dapp))
in (_156_1933)::[])
end
| _77_2653 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _156_1940 = (let _156_1939 = (let _156_1938 = (let _156_1937 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _156_1936 = (let _156_1935 = (let _156_1934 = (FStar_SMTEncoding_Term.mk_and_l prec)
in (ty_pred, _156_1934))
in (FStar_SMTEncoding_Term.mkImp _156_1935))
in (((ty_pred)::[])::[], _156_1937, _156_1936)))
in (FStar_SMTEncoding_Term.mkForall _156_1938))
in (_156_1939, Some ("subterm ordering")))
in FStar_SMTEncoding_Term.Assume (_156_1940)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _77_2657 -> begin
(
# 1556 "FStar.SMTEncoding.Encode.fst"
let _77_2658 = (let _156_1943 = (let _156_1942 = (FStar_Syntax_Print.lid_to_string d)
in (let _156_1941 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _156_1942 _156_1941)))
in (FStar_TypeChecker_Errors.warn drange _156_1943))
in ([], []))
end)
end))
end))
in (
# 1559 "FStar.SMTEncoding.Encode.fst"
let _77_2662 = (encode_elim ())
in (match (_77_2662) with
| (decls2, elim) -> begin
(
# 1560 "FStar.SMTEncoding.Encode.fst"
let g = (let _156_1968 = (let _156_1967 = (let _156_1952 = (let _156_1951 = (let _156_1950 = (let _156_1949 = (let _156_1948 = (let _156_1947 = (let _156_1946 = (let _156_1945 = (let _156_1944 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _156_1944))
in Some (_156_1945))
in (ddtok, [], FStar_SMTEncoding_Term.Term_sort, _156_1946))
in FStar_SMTEncoding_Term.DeclFun (_156_1947))
in (_156_1948)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _156_1949))
in (FStar_List.append _156_1950 proxy_fresh))
in (FStar_List.append _156_1951 decls_formals))
in (FStar_List.append _156_1952 decls_pred))
in (let _156_1966 = (let _156_1965 = (let _156_1964 = (let _156_1956 = (let _156_1955 = (let _156_1954 = (let _156_1953 = (FStar_SMTEncoding_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _156_1953))
in (FStar_SMTEncoding_Term.mkForall _156_1954))
in (_156_1955, Some ("equality for proxy")))
in FStar_SMTEncoding_Term.Assume (_156_1956))
in (let _156_1963 = (let _156_1962 = (let _156_1961 = (let _156_1960 = (let _156_1959 = (let _156_1958 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) vars')
in (let _156_1957 = (FStar_SMTEncoding_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _156_1958, _156_1957)))
in (FStar_SMTEncoding_Term.mkForall _156_1959))
in (_156_1960, Some ("data constructor typing intro")))
in FStar_SMTEncoding_Term.Assume (_156_1961))
in (_156_1962)::[])
in (_156_1964)::_156_1963))
in (FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_156_1965)
in (FStar_List.append _156_1967 _156_1966)))
in (FStar_List.append _156_1968 elim))
in ((FStar_List.append datacons g), env))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end))
end)))))
and declare_top_level_let : env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * FStar_SMTEncoding_Term.term Prims.option) * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (match ((try_lookup_lid env x)) with
| None -> begin
(
# 1578 "FStar.SMTEncoding.Encode.fst"
let _77_2671 = (encode_free_var env x t t_norm [])
in (match (_77_2671) with
| (decls, env) -> begin
(
# 1579 "FStar.SMTEncoding.Encode.fst"
let _77_2676 = (lookup_lid env x)
in (match (_77_2676) with
| (n, x', _77_2675) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _77_2680) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env lid t -> (
# 1585 "FStar.SMTEncoding.Encode.fst"
let _77_2688 = (encode_function_type_as_formula None None t env)
in (match (_77_2688) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)))))::[]))
end)))
and encode_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid tt t_norm quals -> if ((let _156_1981 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _156_1981)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(
# 1591 "FStar.SMTEncoding.Encode.fst"
let _77_2697 = (new_term_constant_and_tok_from_lid env lid)
in (match (_77_2697) with
| (vname, vtok, env) -> begin
(
# 1592 "FStar.SMTEncoding.Encode.fst"
let arg_sorts = (match ((let _156_1982 = (FStar_Syntax_Subst.compress t_norm)
in _156_1982.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _77_2700) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _77_2703 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _77_2706 -> begin
[]
end)
in (
# 1595 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.DeclFun ((vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (
# 1596 "FStar.SMTEncoding.Encode.fst"
let dd = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(
# 1599 "FStar.SMTEncoding.Encode.fst"
let vname = (varops.new_fvar lid)
in (
# 1600 "FStar.SMTEncoding.Encode.fst"
let definition = (prims.mk lid vname)
in (
# 1601 "FStar.SMTEncoding.Encode.fst"
let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(
# 1603 "FStar.SMTEncoding.Encode.fst"
let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (
# 1604 "FStar.SMTEncoding.Encode.fst"
let _77_2721 = (
# 1605 "FStar.SMTEncoding.Encode.fst"
let _77_2716 = (curried_arrow_formals_comp t_norm)
in (match (_77_2716) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _156_1984 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _156_1984))
end else begin
(args, (None, (FStar_Syntax_Util.comp_result comp)))
end
end))
in (match (_77_2721) with
| (formals, (pre_opt, res_t)) -> begin
(
# 1609 "FStar.SMTEncoding.Encode.fst"
let _77_2725 = (new_term_constant_and_tok_from_lid env lid)
in (match (_77_2725) with
| (vname, vtok, env) -> begin
(
# 1610 "FStar.SMTEncoding.Encode.fst"
let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
end
| _77_2728 -> begin
(FStar_SMTEncoding_Term.mkApp (vtok, []))
end)
in (
# 1613 "FStar.SMTEncoding.Encode.fst"
let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _77_20 -> (match (_77_20) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(
# 1615 "FStar.SMTEncoding.Encode.fst"
let _77_2744 = (FStar_Util.prefix vars)
in (match (_77_2744) with
| (_77_2739, (xxsym, _77_2742)) -> begin
(
# 1616 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let _156_2001 = (let _156_2000 = (let _156_1999 = (let _156_1998 = (let _156_1997 = (let _156_1996 = (let _156_1995 = (let _156_1994 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _156_1994))
in (vapp, _156_1995))
in (FStar_SMTEncoding_Term.mkEq _156_1996))
in (((vapp)::[])::[], vars, _156_1997))
in (FStar_SMTEncoding_Term.mkForall _156_1998))
in (_156_1999, Some ("Discriminator equation")))
in FStar_SMTEncoding_Term.Assume (_156_2000))
in (_156_2001)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(
# 1621 "FStar.SMTEncoding.Encode.fst"
let _77_2756 = (FStar_Util.prefix vars)
in (match (_77_2756) with
| (_77_2751, (xxsym, _77_2754)) -> begin
(
# 1622 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (
# 1623 "FStar.SMTEncoding.Encode.fst"
let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (
# 1624 "FStar.SMTEncoding.Encode.fst"
let prim_app = (let _156_2003 = (let _156_2002 = (mk_term_projector_name d f)
in (_156_2002, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _156_2003))
in (let _156_2008 = (let _156_2007 = (let _156_2006 = (let _156_2005 = (let _156_2004 = (FStar_SMTEncoding_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _156_2004))
in (FStar_SMTEncoding_Term.mkForall _156_2005))
in (_156_2006, Some ("Projector equation")))
in FStar_SMTEncoding_Term.Assume (_156_2007))
in (_156_2008)::[]))))
end))
end
| _77_2761 -> begin
[]
end)))))
in (
# 1628 "FStar.SMTEncoding.Encode.fst"
let _77_2768 = (encode_binders None formals env)
in (match (_77_2768) with
| (vars, guards, env', decls1, _77_2767) -> begin
(
# 1629 "FStar.SMTEncoding.Encode.fst"
let _77_2777 = (match (pre_opt) with
| None -> begin
(let _156_2009 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_156_2009, decls1))
end
| Some (p) -> begin
(
# 1631 "FStar.SMTEncoding.Encode.fst"
let _77_2774 = (encode_formula p env')
in (match (_77_2774) with
| (g, ds) -> begin
(let _156_2010 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in (_156_2010, (FStar_List.append decls1 ds)))
end))
end)
in (match (_77_2777) with
| (guard, decls1) -> begin
(
# 1632 "FStar.SMTEncoding.Encode.fst"
let vtok_app = (mk_Apply vtok_tm vars)
in (
# 1634 "FStar.SMTEncoding.Encode.fst"
let vapp = (let _156_2012 = (let _156_2011 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (vname, _156_2011))
in (FStar_SMTEncoding_Term.mkApp _156_2012))
in (
# 1635 "FStar.SMTEncoding.Encode.fst"
let _77_2801 = (
# 1636 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _156_2015 = (let _156_2014 = (FStar_All.pipe_right formals (FStar_List.map (fun _77_2780 -> FStar_SMTEncoding_Term.Term_sort)))
in (vname, _156_2014, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_156_2015))
in (
# 1637 "FStar.SMTEncoding.Encode.fst"
let _77_2788 = (
# 1638 "FStar.SMTEncoding.Encode.fst"
let env = (
# 1638 "FStar.SMTEncoding.Encode.fst"
let _77_2783 = env
in {bindings = _77_2783.bindings; depth = _77_2783.depth; tcenv = _77_2783.tcenv; warn = _77_2783.warn; cache = _77_2783.cache; nolabels = _77_2783.nolabels; use_zfuel_name = _77_2783.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_77_2788) with
| (tok_typing, decls2) -> begin
(
# 1642 "FStar.SMTEncoding.Encode.fst"
let tok_typing = FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("function token typing")))
in (
# 1643 "FStar.SMTEncoding.Encode.fst"
let _77_2798 = (match (formals) with
| [] -> begin
(let _156_2019 = (let _156_2018 = (let _156_2017 = (FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
in (FStar_All.pipe_left (fun _156_2016 -> Some (_156_2016)) _156_2017))
in (push_free_var env lid vname _156_2018))
in ((FStar_List.append decls2 ((tok_typing)::[])), _156_2019))
end
| _77_2792 -> begin
(
# 1646 "FStar.SMTEncoding.Encode.fst"
let vtok_decl = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, None))
in (
# 1647 "FStar.SMTEncoding.Encode.fst"
let vtok_fresh = (let _156_2020 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (vtok, FStar_SMTEncoding_Term.Term_sort) _156_2020))
in (
# 1648 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _156_2024 = (let _156_2023 = (let _156_2022 = (let _156_2021 = (FStar_SMTEncoding_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _156_2021))
in (FStar_SMTEncoding_Term.mkForall _156_2022))
in (_156_2023, None))
in FStar_SMTEncoding_Term.Assume (_156_2024))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_77_2798) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_77_2801) with
| (decls2, env) -> begin
(
# 1651 "FStar.SMTEncoding.Encode.fst"
let _77_2809 = (
# 1652 "FStar.SMTEncoding.Encode.fst"
let res_t = (FStar_Syntax_Subst.compress res_t)
in (
# 1653 "FStar.SMTEncoding.Encode.fst"
let _77_2805 = (encode_term res_t env')
in (match (_77_2805) with
| (encoded_res_t, decls) -> begin
(let _156_2025 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _156_2025, decls))
end)))
in (match (_77_2809) with
| (encoded_res_t, ty_pred, decls3) -> begin
(
# 1655 "FStar.SMTEncoding.Encode.fst"
let typingAx = (let _156_2029 = (let _156_2028 = (let _156_2027 = (let _156_2026 = (FStar_SMTEncoding_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _156_2026))
in (FStar_SMTEncoding_Term.mkForall _156_2027))
in (_156_2028, Some ("free var typing")))
in FStar_SMTEncoding_Term.Assume (_156_2029))
in (
# 1656 "FStar.SMTEncoding.Encode.fst"
let g = (let _156_2031 = (let _156_2030 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_156_2030)
in (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) _156_2031))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end
end)
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _77_2816 se -> (match (_77_2816) with
| (g, env) -> begin
(
# 1662 "FStar.SMTEncoding.Encode.fst"
let _77_2820 = (encode_sigelt env se)
in (match (_77_2820) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

# 1665 "FStar.SMTEncoding.Encode.fst"
let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (
# 1690 "FStar.SMTEncoding.Encode.fst"
let encode_binding = (fun b _77_2827 -> (match (_77_2827) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_77_2829) -> begin
([], env)
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(
# 1695 "FStar.SMTEncoding.Encode.fst"
let _77_2836 = (new_term_constant env x)
in (match (_77_2836) with
| (xxsym, xx, env') -> begin
(
# 1696 "FStar.SMTEncoding.Encode.fst"
let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (
# 1697 "FStar.SMTEncoding.Encode.fst"
let _77_2838 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _156_2046 = (FStar_Syntax_Print.bv_to_string x)
in (let _156_2045 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _156_2044 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _156_2046 _156_2045 _156_2044))))
end else begin
()
end
in (
# 1699 "FStar.SMTEncoding.Encode.fst"
let _77_2842 = (encode_term_pred None t1 env xx)
in (match (_77_2842) with
| (t, decls') -> begin
(
# 1700 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _156_2050 = (let _156_2049 = (FStar_Syntax_Print.bv_to_string x)
in (let _156_2048 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _156_2047 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _156_2049 _156_2048 _156_2047))))
in Some (_156_2050))
end else begin
None
end
in (
# 1704 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun ((xxsym, [], FStar_SMTEncoding_Term.Term_sort, caption)))::[]) decls') ((FStar_SMTEncoding_Term.Assume ((t, None)))::[]))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_77_2847, t)) -> begin
(
# 1710 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env t)
in (
# 1712 "FStar.SMTEncoding.Encode.fst"
let _77_2855 = (encode_free_var env x t t_norm [])
in (match (_77_2855) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end)))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(
# 1717 "FStar.SMTEncoding.Encode.fst"
let _77_2869 = (encode_sigelt env se)
in (match (_77_2869) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

# 1722 "FStar.SMTEncoding.Encode.fst"
let encode_labels = (fun labs -> (
# 1723 "FStar.SMTEncoding.Encode.fst"
let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _77_2876 -> (match (_77_2876) with
| (l, _77_2873, _77_2875) -> begin
FStar_SMTEncoding_Term.DeclFun (((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))
end))))
in (
# 1724 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _77_2883 -> (match (_77_2883) with
| (l, _77_2880, _77_2882) -> begin
(let _156_2058 = (FStar_All.pipe_left (fun _156_2054 -> FStar_SMTEncoding_Term.Echo (_156_2054)) (Prims.fst l))
in (let _156_2057 = (let _156_2056 = (let _156_2055 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_156_2055))
in (_156_2056)::[])
in (_156_2058)::_156_2057))
end))))
in (prefix, suffix))))

# 1728 "FStar.SMTEncoding.Encode.fst"
let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 1729 "FStar.SMTEncoding.Encode.fst"
let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _156_2063 = (let _156_2062 = (let _156_2061 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _156_2061; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_156_2062)::[])
in (FStar_ST.op_Colon_Equals last_env _156_2063)))

# 1732 "FStar.SMTEncoding.Encode.fst"
let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_77_2889 -> begin
(
# 1734 "FStar.SMTEncoding.Encode.fst"
let _77_2892 = e
in {bindings = _77_2892.bindings; depth = _77_2892.depth; tcenv = tcenv; warn = _77_2892.warn; cache = _77_2892.cache; nolabels = _77_2892.nolabels; use_zfuel_name = _77_2892.use_zfuel_name; encode_non_total_function_typ = _77_2892.encode_non_total_function_typ})
end))

# 1735 "FStar.SMTEncoding.Encode.fst"
let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _77_2898::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

# 1738 "FStar.SMTEncoding.Encode.fst"
let push_env : Prims.unit  ->  Prims.unit = (fun _77_2900 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(
# 1741 "FStar.SMTEncoding.Encode.fst"
let refs = (FStar_Util.smap_copy hd.cache)
in (
# 1742 "FStar.SMTEncoding.Encode.fst"
let top = (
# 1742 "FStar.SMTEncoding.Encode.fst"
let _77_2906 = hd
in {bindings = _77_2906.bindings; depth = _77_2906.depth; tcenv = _77_2906.tcenv; warn = _77_2906.warn; cache = refs; nolabels = _77_2906.nolabels; use_zfuel_name = _77_2906.use_zfuel_name; encode_non_total_function_typ = _77_2906.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

# 1744 "FStar.SMTEncoding.Encode.fst"
let pop_env : Prims.unit  ->  Prims.unit = (fun _77_2909 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _77_2913::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

# 1747 "FStar.SMTEncoding.Encode.fst"
let mark_env : Prims.unit  ->  Prims.unit = (fun _77_2915 -> (match (()) with
| () -> begin
(push_env ())
end))

# 1748 "FStar.SMTEncoding.Encode.fst"
let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _77_2916 -> (match (()) with
| () -> begin
(pop_env ())
end))

# 1749 "FStar.SMTEncoding.Encode.fst"
let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _77_2917 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_77_2920::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _77_2925 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 1755 "FStar.SMTEncoding.Encode.fst"
let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (
# 1756 "FStar.SMTEncoding.Encode.fst"
let _77_2927 = (init_env tcenv)
in (
# 1757 "FStar.SMTEncoding.Encode.fst"
let _77_2929 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))

# 1759 "FStar.SMTEncoding.Encode.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 1760 "FStar.SMTEncoding.Encode.fst"
let _77_2932 = (push_env ())
in (
# 1761 "FStar.SMTEncoding.Encode.fst"
let _77_2934 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))

# 1763 "FStar.SMTEncoding.Encode.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 1764 "FStar.SMTEncoding.Encode.fst"
let _77_2937 = (let _156_2084 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _156_2084))
in (
# 1765 "FStar.SMTEncoding.Encode.fst"
let _77_2939 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))

# 1767 "FStar.SMTEncoding.Encode.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1768 "FStar.SMTEncoding.Encode.fst"
let _77_2942 = (mark_env ())
in (
# 1769 "FStar.SMTEncoding.Encode.fst"
let _77_2944 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))

# 1771 "FStar.SMTEncoding.Encode.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1772 "FStar.SMTEncoding.Encode.fst"
let _77_2947 = (reset_mark_env ())
in (
# 1773 "FStar.SMTEncoding.Encode.fst"
let _77_2949 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))

# 1775 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun msg -> (
# 1776 "FStar.SMTEncoding.Encode.fst"
let _77_2952 = (commit_mark_env ())
in (
# 1777 "FStar.SMTEncoding.Encode.fst"
let _77_2954 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))

# 1779 "FStar.SMTEncoding.Encode.fst"
let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (
# 1780 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _156_2100 = (let _156_2099 = (let _156_2098 = (let _156_2097 = (let _156_2096 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _156_2096 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _156_2097 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _156_2098))
in FStar_SMTEncoding_Term.Caption (_156_2099))
in (_156_2100)::decls)
end else begin
decls
end)
in (
# 1784 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1785 "FStar.SMTEncoding.Encode.fst"
let _77_2963 = (encode_sigelt env se)
in (match (_77_2963) with
| (decls, env) -> begin
(
# 1786 "FStar.SMTEncoding.Encode.fst"
let _77_2964 = (set_env env)
in (let _156_2101 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _156_2101)))
end)))))

# 1789 "FStar.SMTEncoding.Encode.fst"
let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (
# 1790 "FStar.SMTEncoding.Encode.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 1791 "FStar.SMTEncoding.Encode.fst"
let _77_2969 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _156_2106 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _156_2106))
end else begin
()
end
in (
# 1793 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1794 "FStar.SMTEncoding.Encode.fst"
let _77_2976 = (encode_signature (
# 1794 "FStar.SMTEncoding.Encode.fst"
let _77_2972 = env
in {bindings = _77_2972.bindings; depth = _77_2972.depth; tcenv = _77_2972.tcenv; warn = false; cache = _77_2972.cache; nolabels = _77_2972.nolabels; use_zfuel_name = _77_2972.use_zfuel_name; encode_non_total_function_typ = _77_2972.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_77_2976) with
| (decls, env) -> begin
(
# 1795 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(
# 1797 "FStar.SMTEncoding.Encode.fst"
let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (
# 1800 "FStar.SMTEncoding.Encode.fst"
let _77_2982 = (set_env (
# 1800 "FStar.SMTEncoding.Encode.fst"
let _77_2980 = env
in {bindings = _77_2980.bindings; depth = _77_2980.depth; tcenv = _77_2980.tcenv; warn = true; cache = _77_2980.cache; nolabels = _77_2980.nolabels; use_zfuel_name = _77_2980.use_zfuel_name; encode_non_total_function_typ = _77_2980.encode_non_total_function_typ}))
in (
# 1801 "FStar.SMTEncoding.Encode.fst"
let _77_2984 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (
# 1802 "FStar.SMTEncoding.Encode.fst"
let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))

# 1805 "FStar.SMTEncoding.Encode.fst"
let solve : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun tcenv q -> (
# 1806 "FStar.SMTEncoding.Encode.fst"
let _77_2989 = (let _156_2115 = (let _156_2114 = (let _156_2113 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _156_2113))
in (FStar_Util.format1 "Starting query at %s" _156_2114))
in (push _156_2115))
in (
# 1807 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _77_2992 -> (match (()) with
| () -> begin
(let _156_2120 = (let _156_2119 = (let _156_2118 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _156_2118))
in (FStar_Util.format1 "Ending query at %s" _156_2119))
in (pop _156_2120))
end))
in (
# 1808 "FStar.SMTEncoding.Encode.fst"
let _77_3046 = (
# 1809 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1810 "FStar.SMTEncoding.Encode.fst"
let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (
# 1811 "FStar.SMTEncoding.Encode.fst"
let _77_3016 = (
# 1812 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun bindings -> (match (bindings) with
| FStar_TypeChecker_Env.Binding_var (x)::rest -> begin
(
# 1814 "FStar.SMTEncoding.Encode.fst"
let _77_3005 = (aux rest)
in (match (_77_3005) with
| (out, rest) -> begin
(
# 1815 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _156_2126 = (let _156_2125 = (FStar_Syntax_Syntax.mk_binder (
# 1816 "FStar.SMTEncoding.Encode.fst"
let _77_3007 = x
in {FStar_Syntax_Syntax.ppname = _77_3007.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _77_3007.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_156_2125)::out)
in (_156_2126, rest)))
end))
end
| _77_3010 -> begin
([], bindings)
end))
in (
# 1818 "FStar.SMTEncoding.Encode.fst"
let _77_3013 = (aux bindings)
in (match (_77_3013) with
| (closing, bindings) -> begin
(let _156_2127 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in (_156_2127, bindings))
end)))
in (match (_77_3016) with
| (q, bindings) -> begin
(
# 1820 "FStar.SMTEncoding.Encode.fst"
let _77_3025 = (let _156_2129 = (FStar_List.filter (fun _77_21 -> (match (_77_21) with
| FStar_TypeChecker_Env.Binding_sig (_77_3019) -> begin
false
end
| _77_3022 -> begin
true
end)) bindings)
in (encode_env_bindings env _156_2129))
in (match (_77_3025) with
| (env_decls, env) -> begin
(
# 1821 "FStar.SMTEncoding.Encode.fst"
let _77_3026 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _156_2130 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _156_2130))
end else begin
()
end
in (
# 1822 "FStar.SMTEncoding.Encode.fst"
let _77_3030 = (encode_formula q env)
in (match (_77_3030) with
| (phi, qdecls) -> begin
(
# 1825 "FStar.SMTEncoding.Encode.fst"
let _77_3035 = (FStar_SMTEncoding_ErrorReporting.label_goals [] phi [])
in (match (_77_3035) with
| (phi, labels, _77_3034) -> begin
(
# 1826 "FStar.SMTEncoding.Encode.fst"
let _77_3038 = (encode_labels labels)
in (match (_77_3038) with
| (label_prefix, label_suffix) -> begin
(
# 1827 "FStar.SMTEncoding.Encode.fst"
let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (
# 1831 "FStar.SMTEncoding.Encode.fst"
let qry = (let _156_2132 = (let _156_2131 = (FStar_SMTEncoding_Term.mkNot phi)
in (_156_2131, Some ("query")))
in FStar_SMTEncoding_Term.Assume (_156_2132))
in (
# 1832 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end))
end)))
end))
end))))
in (match (_77_3046) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _77_3053); FStar_SMTEncoding_Term.hash = _77_3050; FStar_SMTEncoding_Term.freevars = _77_3048}, _77_3058) -> begin
(
# 1835 "FStar.SMTEncoding.Encode.fst"
let _77_3061 = (pop ())
in ())
end
| _77_3064 when tcenv.FStar_TypeChecker_Env.admit -> begin
(
# 1836 "FStar.SMTEncoding.Encode.fst"
let _77_3065 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _77_3069) -> begin
(
# 1838 "FStar.SMTEncoding.Encode.fst"
let fresh = ((FStar_String.length q.FStar_SMTEncoding_Term.hash) >= 2048)
in (
# 1839 "FStar.SMTEncoding.Encode.fst"
let _77_3073 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (
# 1841 "FStar.SMTEncoding.Encode.fst"
let with_fuel = (fun p _77_3079 -> (match (_77_3079) with
| (n, i) -> begin
(let _156_2155 = (let _156_2154 = (let _156_2139 = (let _156_2138 = (FStar_Util.string_of_int n)
in (let _156_2137 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _156_2138 _156_2137)))
in FStar_SMTEncoding_Term.Caption (_156_2139))
in (let _156_2153 = (let _156_2152 = (let _156_2144 = (let _156_2143 = (let _156_2142 = (let _156_2141 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _156_2140 = (FStar_SMTEncoding_Term.n_fuel n)
in (_156_2141, _156_2140)))
in (FStar_SMTEncoding_Term.mkEq _156_2142))
in (_156_2143, None))
in FStar_SMTEncoding_Term.Assume (_156_2144))
in (let _156_2151 = (let _156_2150 = (let _156_2149 = (let _156_2148 = (let _156_2147 = (let _156_2146 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _156_2145 = (FStar_SMTEncoding_Term.n_fuel i)
in (_156_2146, _156_2145)))
in (FStar_SMTEncoding_Term.mkEq _156_2147))
in (_156_2148, None))
in FStar_SMTEncoding_Term.Assume (_156_2149))
in (_156_2150)::(p)::(FStar_SMTEncoding_Term.CheckSat)::[])
in (_156_2152)::_156_2151))
in (_156_2154)::_156_2153))
in (FStar_List.append _156_2155 suffix))
end))
in (
# 1848 "FStar.SMTEncoding.Encode.fst"
let check = (fun p -> (
# 1849 "FStar.SMTEncoding.Encode.fst"
let initial_config = (let _156_2159 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _156_2158 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_156_2159, _156_2158)))
in (
# 1850 "FStar.SMTEncoding.Encode.fst"
let alt_configs = (let _156_2178 = (let _156_2177 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _156_2162 = (let _156_2161 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _156_2160 = (FStar_ST.read FStar_Options.max_ifuel)
in (_156_2161, _156_2160)))
in (_156_2162)::[])
end else begin
[]
end
in (let _156_2176 = (let _156_2175 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _156_2165 = (let _156_2164 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _156_2163 = (FStar_ST.read FStar_Options.max_ifuel)
in (_156_2164, _156_2163)))
in (_156_2165)::[])
end else begin
[]
end
in (let _156_2174 = (let _156_2173 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _156_2168 = (let _156_2167 = (FStar_ST.read FStar_Options.max_fuel)
in (let _156_2166 = (FStar_ST.read FStar_Options.max_ifuel)
in (_156_2167, _156_2166)))
in (_156_2168)::[])
end else begin
[]
end
in (let _156_2172 = (let _156_2171 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _156_2170 = (let _156_2169 = (FStar_ST.read FStar_Options.min_fuel)
in (_156_2169, 1))
in (_156_2170)::[])
end else begin
[]
end
in (_156_2171)::[])
in (_156_2173)::_156_2172))
in (_156_2175)::_156_2174))
in (_156_2177)::_156_2176))
in (FStar_List.flatten _156_2178))
in (
# 1855 "FStar.SMTEncoding.Encode.fst"
let report = (fun errs -> (
# 1856 "FStar.SMTEncoding.Encode.fst"
let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Range.dummyRange))::[]
end
| _77_3088 -> begin
errs
end)
in (
# 1859 "FStar.SMTEncoding.Encode.fst"
let _77_3090 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _156_2186 = (let _156_2181 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_Range.string_of_range _156_2181))
in (let _156_2185 = (let _156_2182 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _156_2182 FStar_Util.string_of_int))
in (let _156_2184 = (let _156_2183 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _156_2183 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _156_2186 _156_2185 _156_2184))))
end else begin
()
end
in (FStar_TypeChecker_Errors.add_errors tcenv errs))))
in (
# 1866 "FStar.SMTEncoding.Encode.fst"
let rec try_alt_configs = (fun p errs _77_22 -> (match (_77_22) with
| [] -> begin
(report errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _156_2197 = (with_fuel p mi)
in (FStar_SMTEncoding_Z3.ask fresh labels _156_2197 (cb mi p [])))
end
| _77_3102 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _156_2199 = (with_fuel p mi)
in (FStar_SMTEncoding_Z3.ask fresh labels _156_2199 (fun _77_3108 -> (match (_77_3108) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _77_3111 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _77_3114 p alt _77_3119 -> (match ((_77_3114, _77_3119)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _156_2207 = (let _156_2204 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_Range.string_of_range _156_2204))
in (let _156_2206 = (FStar_Util.string_of_int prev_fuel)
in (let _156_2205 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _156_2207 _156_2206 _156_2205))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _156_2208 = (with_fuel p initial_config)
in (FStar_SMTEncoding_Z3.ask fresh labels _156_2208 (cb initial_config p alt_configs))))))))
in (
# 1891 "FStar.SMTEncoding.Encode.fst"
let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 1893 "FStar.SMTEncoding.Encode.fst"
let _77_3124 = (let _156_2214 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _156_2214 q))
in (match (_77_3124) with
| (b, cb) -> begin
if b then begin
(FStar_SMTEncoding_SplitQueryCases.handle_query cb check)
end else begin
(check q)
end
end))
end else begin
(check q)
end)
in (
# 1898 "FStar.SMTEncoding.Encode.fst"
let _77_3125 = if (FStar_ST.read FStar_Options.admit_smt_queries) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end
| _77_3128 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))

# 1904 "FStar.SMTEncoding.Encode.fst"
let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (
# 1905 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1906 "FStar.SMTEncoding.Encode.fst"
let _77_3132 = (push "query")
in (
# 1907 "FStar.SMTEncoding.Encode.fst"
let _77_3139 = (encode_formula_with_labels q env)
in (match (_77_3139) with
| (f, _77_3136, _77_3138) -> begin
(
# 1908 "FStar.SMTEncoding.Encode.fst"
let _77_3140 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _77_3144) -> begin
true
end
| _77_3148 -> begin
false
end))
end)))))

# 1913 "FStar.SMTEncoding.Encode.fst"
let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = init; FStar_TypeChecker_Env.push = push; FStar_TypeChecker_Env.pop = pop; FStar_TypeChecker_Env.mark = mark; FStar_TypeChecker_Env.reset_mark = reset_mark; FStar_TypeChecker_Env.commit_mark = commit_mark; FStar_TypeChecker_Env.encode_modul = encode_modul; FStar_TypeChecker_Env.encode_sig = encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}

# 1927 "FStar.SMTEncoding.Encode.fst"
let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _77_3149 -> ()); FStar_TypeChecker_Env.push = (fun _77_3151 -> ()); FStar_TypeChecker_Env.pop = (fun _77_3153 -> ()); FStar_TypeChecker_Env.mark = (fun _77_3155 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _77_3157 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _77_3159 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _77_3161 _77_3163 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _77_3165 _77_3167 -> ()); FStar_TypeChecker_Env.solve = (fun _77_3169 _77_3171 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _77_3173 _77_3175 -> false); FStar_TypeChecker_Env.finish = (fun _77_3177 -> ()); FStar_TypeChecker_Env.refresh = (fun _77_3178 -> ())}





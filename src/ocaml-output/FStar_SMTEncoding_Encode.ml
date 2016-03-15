
open Prims
# 34 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun x tl -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
tl
end else begin
(x)::tl
end)

# 35 "FStar.SMTEncoding.Encode.fst"
let withenv = (fun c _78_28 -> (match (_78_28) with
| (a, b) -> begin
(a, b, c)
end))

# 36 "FStar.SMTEncoding.Encode.fst"
let vargs = (fun args -> (FStar_List.filter (fun _78_1 -> (match (_78_1) with
| (FStar_Util.Inl (_78_32), _78_35) -> begin
false
end
| _78_38 -> begin
true
end)) args))

# 37 "FStar.SMTEncoding.Encode.fst"
let subst_lcomp_opt : FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_Syntax_Syntax.lcomp Prims.option  ->  FStar_Syntax_Syntax.lcomp Prims.option = (fun s l -> (match (l) with
| None -> begin
None
end
| Some (l) -> begin
(let _162_13 = (let _162_12 = (let _162_11 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s _162_11))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp _162_12))
in Some (_162_13))
end))

# 42 "FStar.SMTEncoding.Encode.fst"
let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))

# 43 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (
# 44 "FStar.SMTEncoding.Encode.fst"
let a = (
# 44 "FStar.SMTEncoding.Encode.fst"
let _78_47 = a
in (let _162_20 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _162_20; FStar_Syntax_Syntax.index = _78_47.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _78_47.FStar_Syntax_Syntax.sort}))
in (let _162_21 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape _162_21))))

# 46 "FStar.SMTEncoding.Encode.fst"
let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (
# 47 "FStar.SMTEncoding.Encode.fst"
let fail = (fun _78_54 -> (match (()) with
| () -> begin
(let _162_31 = (let _162_30 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _162_30 lid.FStar_Ident.str))
in (FStar_All.failwith _162_31))
end))
in (
# 48 "FStar.SMTEncoding.Encode.fst"
let _78_58 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (_78_58) with
| (_78_56, t) -> begin
(match ((let _162_32 = (FStar_Syntax_Subst.compress t)
in _162_32.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(
# 51 "FStar.SMTEncoding.Encode.fst"
let _78_66 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_78_66) with
| (binders, _78_65) -> begin
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
| _78_69 -> begin
(fail ())
end)
end))))

# 57 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _162_38 = (let _162_37 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _162_37))
in (FStar_All.pipe_left escape _162_38)))

# 58 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (let _162_44 = (let _162_43 = (mk_term_projector_name lid a)
in (_162_43, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _162_44)))

# 60 "FStar.SMTEncoding.Encode.fst"
let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (let _162_50 = (let _162_49 = (mk_term_projector_name_by_pos lid i)
in (_162_49, FStar_SMTEncoding_Term.Arrow ((FStar_SMTEncoding_Term.Term_sort, FStar_SMTEncoding_Term.Term_sort))))
in (FStar_SMTEncoding_Term.mkFreeV _162_50)))

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
let initial_ctr = 100
in (
# 79 "FStar.SMTEncoding.Encode.fst"
let ctr = (FStar_Util.mk_ref initial_ctr)
in (
# 80 "FStar.SMTEncoding.Encode.fst"
let new_scope = (fun _78_93 -> (match (()) with
| () -> begin
(let _162_154 = (FStar_Util.smap_create 100)
in (let _162_153 = (FStar_Util.smap_create 100)
in (_162_154, _162_153)))
end))
in (
# 81 "FStar.SMTEncoding.Encode.fst"
let scopes = (let _162_156 = (let _162_155 = (new_scope ())
in (_162_155)::[])
in (FStar_Util.mk_ref _162_156))
in (
# 82 "FStar.SMTEncoding.Encode.fst"
let mk_unique = (fun y -> (
# 83 "FStar.SMTEncoding.Encode.fst"
let y = (escape y)
in (
# 84 "FStar.SMTEncoding.Encode.fst"
let y = (match ((let _162_160 = (FStar_ST.read scopes)
in (FStar_Util.find_map _162_160 (fun _78_101 -> (match (_78_101) with
| (names, _78_100) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_78_104) -> begin
(
# 86 "FStar.SMTEncoding.Encode.fst"
let _78_106 = (FStar_Util.incr ctr)
in (let _162_162 = (let _162_161 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _162_161))
in (Prims.strcat (Prims.strcat y "__") _162_162)))
end)
in (
# 87 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _162_164 = (let _162_163 = (FStar_ST.read scopes)
in (FStar_List.hd _162_163))
in (FStar_All.pipe_left Prims.fst _162_164))
in (
# 88 "FStar.SMTEncoding.Encode.fst"
let _78_110 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (
# 89 "FStar.SMTEncoding.Encode.fst"
let new_var = (fun pp rn -> (let _162_171 = (let _162_169 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _162_169 "__"))
in (let _162_170 = (FStar_Util.string_of_int rn)
in (Prims.strcat _162_171 _162_170))))
in (
# 90 "FStar.SMTEncoding.Encode.fst"
let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (
# 91 "FStar.SMTEncoding.Encode.fst"
let next_id = (fun _78_118 -> (match (()) with
| () -> begin
(
# 91 "FStar.SMTEncoding.Encode.fst"
let _78_119 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (
# 92 "FStar.SMTEncoding.Encode.fst"
let fresh = (fun pfx -> (let _162_179 = (let _162_178 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _162_178))
in (FStar_Util.format2 "%s_%s" pfx _162_179)))
in (
# 93 "FStar.SMTEncoding.Encode.fst"
let string_const = (fun s -> (match ((let _162_183 = (FStar_ST.read scopes)
in (FStar_Util.find_map _162_183 (fun _78_128 -> (match (_78_128) with
| (_78_126, strings) -> begin
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
let f = (let _162_184 = (FStar_SMTEncoding_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString _162_184))
in (
# 98 "FStar.SMTEncoding.Encode.fst"
let top_scope = (let _162_186 = (let _162_185 = (FStar_ST.read scopes)
in (FStar_List.hd _162_185))
in (FStar_All.pipe_left Prims.snd _162_186))
in (
# 99 "FStar.SMTEncoding.Encode.fst"
let _78_135 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (
# 101 "FStar.SMTEncoding.Encode.fst"
let push = (fun _78_138 -> (match (()) with
| () -> begin
(let _162_191 = (let _162_190 = (new_scope ())
in (let _162_189 = (FStar_ST.read scopes)
in (_162_190)::_162_189))
in (FStar_ST.op_Colon_Equals scopes _162_191))
end))
in (
# 102 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _78_140 -> (match (()) with
| () -> begin
(let _162_195 = (let _162_194 = (FStar_ST.read scopes)
in (FStar_List.tl _162_194))
in (FStar_ST.op_Colon_Equals scopes _162_195))
end))
in (
# 103 "FStar.SMTEncoding.Encode.fst"
let mark = (fun _78_142 -> (match (()) with
| () -> begin
(push ())
end))
in (
# 104 "FStar.SMTEncoding.Encode.fst"
let reset_mark = (fun _78_144 -> (match (()) with
| () -> begin
(pop ())
end))
in (
# 105 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun _78_146 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(
# 107 "FStar.SMTEncoding.Encode.fst"
let _78_159 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (
# 108 "FStar.SMTEncoding.Encode.fst"
let _78_164 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _78_167 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

# 122 "FStar.SMTEncoding.Encode.fst"
let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (
# 122 "FStar.SMTEncoding.Encode.fst"
let _78_169 = x
in (let _162_210 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = _162_210; FStar_Syntax_Syntax.index = _78_169.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _78_169.FStar_Syntax_Syntax.sort})))

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
| Binding_var (_78_173) -> begin
_78_173
end))

# 128 "FStar.SMTEncoding.Encode.fst"
let ___Binding_fvar____0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_78_176) -> begin
_78_176
end))

# 131 "FStar.SMTEncoding.Encode.fst"
let binder_of_eithervar = (fun v -> (v, None))

# 132 "FStar.SMTEncoding.Encode.fst"
type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

# 132 "FStar.SMTEncoding.Encode.fst"
let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))

# 142 "FStar.SMTEncoding.Encode.fst"
let print_env : env_t  ->  Prims.string = (fun e -> (let _162_268 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _78_2 -> (match (_78_2) with
| Binding_var (x, _78_191) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, _78_196, _78_198, _78_200) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right _162_268 (FStar_String.concat ", "))))

# 147 "FStar.SMTEncoding.Encode.fst"
let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

# 149 "FStar.SMTEncoding.Encode.fst"
let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _162_278 = (FStar_Syntax_Print.term_to_string t)
in Some (_162_278))
end else begin
None
end)

# 154 "FStar.SMTEncoding.Encode.fst"
let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (
# 154 "FStar.SMTEncoding.Encode.fst"
let xsym = (varops.fresh x)
in (let _162_283 = (FStar_SMTEncoding_Term.mkFreeV (xsym, s))
in (xsym, _162_283))))

# 158 "FStar.SMTEncoding.Encode.fst"
let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 159 "FStar.SMTEncoding.Encode.fst"
let ysym = (let _162_288 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _162_288))
in (
# 160 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV (ysym, FStar_SMTEncoding_Term.Term_sort))
in (ysym, y, (
# 161 "FStar.SMTEncoding.Encode.fst"
let _78_214 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _78_214.tcenv; warn = _78_214.warn; cache = _78_214.cache; nolabels = _78_214.nolabels; use_zfuel_name = _78_214.use_zfuel_name; encode_non_total_function_typ = _78_214.encode_non_total_function_typ})))))

# 162 "FStar.SMTEncoding.Encode.fst"
let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (
# 163 "FStar.SMTEncoding.Encode.fst"
let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (
# 164 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkApp (ysym, []))
in (ysym, y, (
# 165 "FStar.SMTEncoding.Encode.fst"
let _78_220 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _78_220.depth; tcenv = _78_220.tcenv; warn = _78_220.warn; cache = _78_220.cache; nolabels = _78_220.nolabels; use_zfuel_name = _78_220.use_zfuel_name; encode_non_total_function_typ = _78_220.encode_non_total_function_typ})))))

# 166 "FStar.SMTEncoding.Encode.fst"
let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (
# 167 "FStar.SMTEncoding.Encode.fst"
let _78_225 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _78_225.depth; tcenv = _78_225.tcenv; warn = _78_225.warn; cache = _78_225.cache; nolabels = _78_225.nolabels; use_zfuel_name = _78_225.use_zfuel_name; encode_non_total_function_typ = _78_225.encode_non_total_function_typ}))

# 168 "FStar.SMTEncoding.Encode.fst"
let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (match ((lookup_binding env (fun _78_3 -> (match (_78_3) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a) -> begin
Some ((b, t))
end
| _78_235 -> begin
None
end)))) with
| None -> begin
(let _162_305 = (let _162_304 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found: %s" _162_304))
in (FStar_All.failwith _162_305))
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
in (let _162_316 = (
# 178 "FStar.SMTEncoding.Encode.fst"
let _78_245 = env
in (let _162_315 = (let _162_314 = (let _162_313 = (let _162_312 = (let _162_311 = (FStar_SMTEncoding_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _162_310 -> Some (_162_310)) _162_311))
in (x, fname, _162_312, None))
in Binding_fvar (_162_313))
in (_162_314)::env.bindings)
in {bindings = _162_315; depth = _78_245.depth; tcenv = _78_245.tcenv; warn = _78_245.warn; cache = _78_245.cache; nolabels = _78_245.nolabels; use_zfuel_name = _78_245.use_zfuel_name; encode_non_total_function_typ = _78_245.encode_non_total_function_typ}))
in (fname, ftok, _162_316)))))

# 179 "FStar.SMTEncoding.Encode.fst"
let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _78_4 -> (match (_78_4) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _78_257 -> begin
None
end))))

# 181 "FStar.SMTEncoding.Encode.fst"
let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _162_327 = (let _162_326 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" _162_326))
in (FStar_All.failwith _162_327))
end
| Some (s) -> begin
s
end))

# 185 "FStar.SMTEncoding.Encode.fst"
let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (
# 186 "FStar.SMTEncoding.Encode.fst"
let _78_267 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _78_267.depth; tcenv = _78_267.tcenv; warn = _78_267.warn; cache = _78_267.cache; nolabels = _78_267.nolabels; use_zfuel_name = _78_267.use_zfuel_name; encode_non_total_function_typ = _78_267.encode_non_total_function_typ}))

# 187 "FStar.SMTEncoding.Encode.fst"
let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (
# 188 "FStar.SMTEncoding.Encode.fst"
let _78_276 = (lookup_lid env x)
in (match (_78_276) with
| (t1, t2, _78_275) -> begin
(
# 189 "FStar.SMTEncoding.Encode.fst"
let t3 = (let _162_344 = (let _162_343 = (let _162_342 = (FStar_SMTEncoding_Term.mkApp ("ZFuel", []))
in (_162_342)::[])
in (f, _162_343))
in (FStar_SMTEncoding_Term.mkApp _162_344))
in (
# 190 "FStar.SMTEncoding.Encode.fst"
let _78_278 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _78_278.depth; tcenv = _78_278.tcenv; warn = _78_278.warn; cache = _78_278.cache; nolabels = _78_278.nolabels; use_zfuel_name = _78_278.use_zfuel_name; encode_non_total_function_typ = _78_278.encode_non_total_function_typ}))
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
| _78_291 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (_78_295, fuel::[]) -> begin
if (let _162_350 = (let _162_349 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right _162_349 Prims.fst))
in (FStar_Util.starts_with _162_350 "fuel")) then begin
(let _162_353 = (let _162_352 = (FStar_SMTEncoding_Term.mkFreeV (name, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_ApplyTF _162_352 fuel))
in (FStar_All.pipe_left (fun _162_351 -> Some (_162_351)) _162_353))
end else begin
Some (t)
end
end
| _78_301 -> begin
Some (t)
end)
end
| _78_303 -> begin
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
(let _162_357 = (let _162_356 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _162_356))
in (FStar_All.failwith _162_357))
end))

# 212 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_name = (fun env a -> (
# 212 "FStar.SMTEncoding.Encode.fst"
let _78_316 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_78_316) with
| (x, _78_313, _78_315) -> begin
x
end)))

# 213 "FStar.SMTEncoding.Encode.fst"
let lookup_free_var_sym = (fun env a -> (
# 214 "FStar.SMTEncoding.Encode.fst"
let _78_322 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (_78_322) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.hash = _78_326; FStar_SMTEncoding_Term.freevars = _78_324}) when env.use_zfuel_name -> begin
(g, zf)
end
| _78_334 -> begin
(match (sym) with
| None -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _78_344 -> begin
(FStar_SMTEncoding_Term.Var (name), [])
end)
end)
end)
end)))

# 225 "FStar.SMTEncoding.Encode.fst"
let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _78_5 -> (match (_78_5) with
| Binding_fvar (_78_349, nm', tok, _78_353) when (nm = nm') -> begin
tok
end
| _78_357 -> begin
None
end))))

# 234 "FStar.SMTEncoding.Encode.fst"
let mkForall_fuel' = (fun n _78_362 -> (match (_78_362) with
| (pats, vars, body) -> begin
(
# 235 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _78_364 -> (match (()) with
| () -> begin
(FStar_SMTEncoding_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(
# 238 "FStar.SMTEncoding.Encode.fst"
let _78_367 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_78_367) with
| (fsym, fterm) -> begin
(
# 239 "FStar.SMTEncoding.Encode.fst"
let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _78_377 -> begin
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
(let _162_374 = (add_fuel guards)
in (FStar_SMTEncoding_Term.mk_and_l _162_374))
end
| _78_390 -> begin
(let _162_375 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _162_375 FStar_List.hd))
end)
in (FStar_SMTEncoding_Term.mkImp (guard, body')))
end
| _78_393 -> begin
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
| (FStar_Syntax_Syntax.Tm_fvar (fv)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(let _162_381 = (FStar_TypeChecker_Env.lookup_definition FStar_TypeChecker_Env.OnlyInline env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _162_381 FStar_Option.isNone))
end
| _78_432 -> begin
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
let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (let _162_394 = (let _162_392 = (FStar_Syntax_Syntax.null_binder t)
in (_162_392)::[])
in (let _162_393 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs _162_394 _162_393 None))))

# 279 "FStar.SMTEncoding.Encode.fst"
let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(let _162_401 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out _162_401))
end
| s -> begin
(
# 282 "FStar.SMTEncoding.Encode.fst"
let _78_444 = ()
in (let _162_402 = (FStar_SMTEncoding_Term.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTT out _162_402)))
end)) e)))

# 283 "FStar.SMTEncoding.Encode.fst"
let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Term.mk_ApplyTT e)))

# 285 "FStar.SMTEncoding.Encode.fst"
let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun _78_6 -> (match (_78_6) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| _78_454 -> begin
false
end))

# 290 "FStar.SMTEncoding.Encode.fst"
let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (
# 291 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun t xs -> (match ((t.FStar_SMTEncoding_Term.tm, xs)) with
| (FStar_SMTEncoding_Term.App (app, f::{FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.hash = _78_465; FStar_SMTEncoding_Term.freevars = _78_463}::[]), x::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), _78_483) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| _78_490 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_78_492, []) -> begin
(
# 302 "FStar.SMTEncoding.Encode.fst"
let fvs = (FStar_SMTEncoding_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _78_498 -> begin
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
let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun _78_7 -> (match (_78_7) with
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
(let _162_456 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt _162_456))
end
| FStar_Const.Const_uint8 (i) -> begin
(let _162_457 = (FStar_SMTEncoding_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_SMTEncoding_Term.boxInt _162_457))
end
| FStar_Const.Const_int (i) -> begin
(let _162_458 = (FStar_SMTEncoding_Term.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt _162_458))
end
| FStar_Const.Const_int32 (i) -> begin
(let _162_462 = (let _162_461 = (let _162_460 = (let _162_459 = (FStar_SMTEncoding_Term.mkInteger32 i)
in (FStar_SMTEncoding_Term.boxInt _162_459))
in (_162_460)::[])
in ("FStar.Int32.Int32", _162_461))
in (FStar_SMTEncoding_Term.mkApp _162_462))
end
| FStar_Const.Const_string (bytes, _78_520) -> begin
(let _162_463 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _162_463))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(let _162_465 = (let _162_464 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" _162_464))
in (FStar_All.failwith _162_465))
end))

# 356 "FStar.SMTEncoding.Encode.fst"
let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (
# 357 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun norm t -> (
# 358 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (_78_534) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (_78_537) -> begin
(let _162_474 = (FStar_Syntax_Util.unrefine t)
in (aux true _162_474))
end
| _78_540 -> begin
if norm then begin
(let _162_475 = (whnf env t)
in (aux false _162_475))
end else begin
(let _162_478 = (let _162_477 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (let _162_476 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _162_477 _162_476)))
in (FStar_All.failwith _162_478))
end
end)))
in (aux true t0)))

# 367 "FStar.SMTEncoding.Encode.fst"
let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (
# 368 "FStar.SMTEncoding.Encode.fst"
let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| _78_548 -> begin
(let _162_481 = (FStar_Syntax_Syntax.mk_Total k)
in ([], _162_481))
end)))

# 374 "FStar.SMTEncoding.Encode.fst"
let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> (
# 381 "FStar.SMTEncoding.Encode.fst"
let _78_552 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _162_531 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _162_531))
end else begin
()
end
in (
# 383 "FStar.SMTEncoding.Encode.fst"
let _78_580 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _78_559 b -> (match (_78_559) with
| (vars, guards, env, decls, names) -> begin
(
# 384 "FStar.SMTEncoding.Encode.fst"
let _78_574 = (
# 385 "FStar.SMTEncoding.Encode.fst"
let x = (unmangle (Prims.fst b))
in (
# 386 "FStar.SMTEncoding.Encode.fst"
let _78_565 = (gen_term_var env x)
in (match (_78_565) with
| (xxsym, xx, env') -> begin
(
# 387 "FStar.SMTEncoding.Encode.fst"
let _78_568 = (let _162_534 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt _162_534 env xx))
in (match (_78_568) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_SMTEncoding_Term.Term_sort), guard_x_t, env', decls', x)
end))
end)))
in (match (_78_574) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_78_580) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 402 "FStar.SMTEncoding.Encode.fst"
let _78_587 = (encode_term t env)
in (match (_78_587) with
| (t, decls) -> begin
(let _162_539 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_162_539, decls))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (
# 406 "FStar.SMTEncoding.Encode.fst"
let _78_594 = (encode_term t env)
in (match (_78_594) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _162_544 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in (_162_544, decls))
end
| Some (f) -> begin
(let _162_545 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in (_162_545, decls))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (
# 414 "FStar.SMTEncoding.Encode.fst"
let t0 = (FStar_Syntax_Subst.compress t)
in (
# 415 "FStar.SMTEncoding.Encode.fst"
let _78_601 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _162_550 = (FStar_Syntax_Print.tag_of_term t)
in (let _162_549 = (FStar_Syntax_Print.tag_of_term t0)
in (let _162_548 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" _162_550 _162_549 _162_548))))
end else begin
()
end
in (match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _162_555 = (let _162_554 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (let _162_553 = (FStar_Syntax_Print.tag_of_term t0)
in (let _162_552 = (FStar_Syntax_Print.term_to_string t0)
in (let _162_551 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _162_554 _162_553 _162_552 _162_551)))))
in (FStar_All.failwith _162_555))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(let _162_557 = (let _162_556 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" _162_556))
in (FStar_All.failwith _162_557))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, _78_612) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, _78_617) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(
# 431 "FStar.SMTEncoding.Encode.fst"
let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(let _162_558 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in (_162_558, []))
end
| FStar_Syntax_Syntax.Tm_type (_78_626) -> begin
(FStar_SMTEncoding_Term.mk_Term_type, [])
end
| FStar_Syntax_Syntax.Tm_uinst (t, _78_630) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(let _162_559 = (encode_const c)
in (_162_559, []))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 447 "FStar.SMTEncoding.Encode.fst"
let _78_641 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_78_641) with
| (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res)) then begin
(
# 451 "FStar.SMTEncoding.Encode.fst"
let _78_648 = (encode_binders None binders env)
in (match (_78_648) with
| (vars, guards, env', decls, _78_647) -> begin
(
# 452 "FStar.SMTEncoding.Encode.fst"
let fsym = (let _162_560 = (varops.fresh "f")
in (_162_560, FStar_SMTEncoding_Term.Term_sort))
in (
# 453 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 454 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 455 "FStar.SMTEncoding.Encode.fst"
let _78_654 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_78_654) with
| (pre_opt, res_t) -> begin
(
# 456 "FStar.SMTEncoding.Encode.fst"
let _78_657 = (encode_term_pred None res_t env' app)
in (match (_78_657) with
| (res_pred, decls') -> begin
(
# 457 "FStar.SMTEncoding.Encode.fst"
let _78_666 = (match (pre_opt) with
| None -> begin
(let _162_561 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_162_561, decls))
end
| Some (pre) -> begin
(
# 460 "FStar.SMTEncoding.Encode.fst"
let _78_663 = (encode_formula pre env')
in (match (_78_663) with
| (guard, decls0) -> begin
(let _162_562 = (FStar_SMTEncoding_Term.mk_and_l ((guard)::guards))
in (_162_562, (FStar_List.append decls decls0)))
end))
end)
in (match (_78_666) with
| (guards, guard_decls) -> begin
(
# 462 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _162_564 = (let _162_563 = (FStar_SMTEncoding_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _162_563))
in (FStar_SMTEncoding_Term.mkForall _162_564))
in (
# 467 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _162_566 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right _162_566 (FStar_List.filter (fun _78_671 -> (match (_78_671) with
| (x, _78_670) -> begin
(x <> (Prims.fst fsym))
end)))))
in (
# 468 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t', sorts, _78_677) -> begin
(let _162_569 = (let _162_568 = (let _162_567 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t', _162_567))
in (FStar_SMTEncoding_Term.mkApp _162_568))
in (_162_569, []))
end
| None -> begin
(
# 474 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Tm_arrow")
in (
# 475 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 476 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _162_570 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (_162_570))
end else begin
None
end
in (
# 481 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, caption))
in (
# 483 "FStar.SMTEncoding.Encode.fst"
let t = (let _162_572 = (let _162_571 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _162_571))
in (FStar_SMTEncoding_Term.mkApp _162_572))
in (
# 484 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 486 "FStar.SMTEncoding.Encode.fst"
let k_assumption = (let _162_574 = (let _162_573 = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_162_573, Some ((Prims.strcat tsym " kinding"))))
in FStar_SMTEncoding_Term.Assume (_162_574))
in (
# 488 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 489 "FStar.SMTEncoding.Encode.fst"
let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (
# 490 "FStar.SMTEncoding.Encode.fst"
let pre_typing = (let _162_581 = (let _162_580 = (let _162_579 = (let _162_578 = (let _162_577 = (let _162_576 = (let _162_575 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _162_575))
in (f_has_t, _162_576))
in (FStar_SMTEncoding_Term.mkImp _162_577))
in (((f_has_t)::[])::[], (fsym)::cvars, _162_578))
in (mkForall_fuel _162_579))
in (_162_580, Some ("pre-typing for functions")))
in FStar_SMTEncoding_Term.Assume (_162_581))
in (
# 491 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _162_585 = (let _162_584 = (let _162_583 = (let _162_582 = (FStar_SMTEncoding_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _162_582))
in (FStar_SMTEncoding_Term.mkForall _162_583))
in (_162_584, Some ((Prims.strcat tsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_162_585))
in (
# 494 "FStar.SMTEncoding.Encode.fst"
let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (
# 495 "FStar.SMTEncoding.Encode.fst"
let _78_693 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(
# 499 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Non_total_Tm_arrow")
in (
# 500 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, [], FStar_SMTEncoding_Term.Term_sort, None))
in (
# 501 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_SMTEncoding_Term.mkApp (tsym, []))
in (
# 502 "FStar.SMTEncoding.Encode.fst"
let t_kinding = (let _162_587 = (let _162_586 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (_162_586, None))
in FStar_SMTEncoding_Term.Assume (_162_587))
in (
# 503 "FStar.SMTEncoding.Encode.fst"
let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)
in (
# 504 "FStar.SMTEncoding.Encode.fst"
let f = (FStar_SMTEncoding_Term.mkFreeV fsym)
in (
# 505 "FStar.SMTEncoding.Encode.fst"
let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (
# 506 "FStar.SMTEncoding.Encode.fst"
let t_interp = (let _162_594 = (let _162_593 = (let _162_592 = (let _162_591 = (let _162_590 = (let _162_589 = (let _162_588 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _162_588))
in (f_has_t, _162_589))
in (FStar_SMTEncoding_Term.mkImp _162_590))
in (((f_has_t)::[])::[], (fsym)::[], _162_591))
in (mkForall_fuel _162_592))
in (_162_593, Some ("pre-typing")))
in FStar_SMTEncoding_Term.Assume (_162_594))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end))
end
| FStar_Syntax_Syntax.Tm_refine (_78_704) -> begin
(
# 513 "FStar.SMTEncoding.Encode.fst"
let _78_724 = (match ((FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = _78_711; FStar_Syntax_Syntax.pos = _78_709; FStar_Syntax_Syntax.vars = _78_707} -> begin
(
# 515 "FStar.SMTEncoding.Encode.fst"
let _78_719 = (FStar_Syntax_Subst.open_term (((x, None))::[]) f)
in (match (_78_719) with
| (b, f) -> begin
(let _162_596 = (let _162_595 = (FStar_List.hd b)
in (Prims.fst _162_595))
in (_162_596, f))
end))
end
| _78_721 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_78_724) with
| (x, f) -> begin
(
# 519 "FStar.SMTEncoding.Encode.fst"
let _78_727 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (_78_727) with
| (base_t, decls) -> begin
(
# 520 "FStar.SMTEncoding.Encode.fst"
let _78_731 = (gen_term_var env x)
in (match (_78_731) with
| (x, xtm, env') -> begin
(
# 521 "FStar.SMTEncoding.Encode.fst"
let _78_734 = (encode_formula f env')
in (match (_78_734) with
| (refinement, decls') -> begin
(
# 523 "FStar.SMTEncoding.Encode.fst"
let _78_737 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_78_737) with
| (fsym, fterm) -> begin
(
# 525 "FStar.SMTEncoding.Encode.fst"
let encoding = (let _162_598 = (let _162_597 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_162_597, refinement))
in (FStar_SMTEncoding_Term.mkAnd _162_598))
in (
# 527 "FStar.SMTEncoding.Encode.fst"
let cvars = (let _162_600 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right _162_600 (FStar_List.filter (fun _78_742 -> (match (_78_742) with
| (y, _78_741) -> begin
((y <> x) && (y <> fsym))
end)))))
in (
# 528 "FStar.SMTEncoding.Encode.fst"
let xfv = (x, FStar_SMTEncoding_Term.Term_sort)
in (
# 529 "FStar.SMTEncoding.Encode.fst"
let ffv = (fsym, FStar_SMTEncoding_Term.Fuel_sort)
in (
# 530 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _78_749, _78_751) -> begin
(let _162_603 = (let _162_602 = (let _162_601 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Term.mkFreeV))
in (t, _162_601))
in (FStar_SMTEncoding_Term.mkApp _162_602))
in (_162_603, []))
end
| None -> begin
(
# 537 "FStar.SMTEncoding.Encode.fst"
let tsym = (varops.fresh "Typ_refine")
in (
# 538 "FStar.SMTEncoding.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 539 "FStar.SMTEncoding.Encode.fst"
let tdecl = FStar_SMTEncoding_Term.DeclFun ((tsym, cvar_sorts, FStar_SMTEncoding_Term.Term_sort, None))
in (
# 540 "FStar.SMTEncoding.Encode.fst"
let t = (let _162_605 = (let _162_604 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (tsym, _162_604))
in (FStar_SMTEncoding_Term.mkApp _162_605))
in (
# 542 "FStar.SMTEncoding.Encode.fst"
let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (
# 543 "FStar.SMTEncoding.Encode.fst"
let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (
# 545 "FStar.SMTEncoding.Encode.fst"
let t_kinding = (FStar_SMTEncoding_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (
# 546 "FStar.SMTEncoding.Encode.fst"
let assumption = (let _162_607 = (let _162_606 = (FStar_SMTEncoding_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _162_606))
in (FStar_SMTEncoding_Term.mkForall _162_607))
in (
# 548 "FStar.SMTEncoding.Encode.fst"
let t_decls = (let _162_614 = (let _162_613 = (let _162_612 = (let _162_611 = (let _162_610 = (let _162_609 = (let _162_608 = (FStar_Syntax_Print.term_to_string t0)
in Some (_162_608))
in (assumption, _162_609))
in FStar_SMTEncoding_Term.Assume (_162_610))
in (_162_611)::[])
in (FStar_SMTEncoding_Term.Assume ((t_kinding, None)))::_162_612)
in (tdecl)::_162_613)
in (FStar_List.append (FStar_List.append decls decls') _162_614))
in (
# 553 "FStar.SMTEncoding.Encode.fst"
let _78_764 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (tsym, cvar_sorts, t_decls))
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
# 558 "FStar.SMTEncoding.Encode.fst"
let ttm = (let _162_615 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Term.mk_Term_uvar _162_615))
in (
# 559 "FStar.SMTEncoding.Encode.fst"
let _78_773 = (encode_term_pred None k env ttm)
in (match (_78_773) with
| (t_has_k, decls) -> begin
(
# 560 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| FStar_Syntax_Syntax.Tm_app (_78_776) -> begin
(
# 564 "FStar.SMTEncoding.Encode.fst"
let _78_780 = (FStar_Syntax_Util.head_and_args t0)
in (match (_78_780) with
| (head, args_e) -> begin
(match ((let _162_617 = (let _162_616 = (FStar_Syntax_Subst.compress head)
in _162_616.FStar_Syntax_Syntax.n)
in (_162_617, args_e))) with
| (FStar_Syntax_Syntax.Tm_abs (_78_782), _78_785) -> begin
(let _162_618 = (whnf env t)
in (encode_term _162_618 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _::(v1, _)::(v2, _)::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), _::(v1, _)::(v2, _)::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(
# 571 "FStar.SMTEncoding.Encode.fst"
let _78_825 = (encode_term v1 env)
in (match (_78_825) with
| (v1, decls1) -> begin
(
# 572 "FStar.SMTEncoding.Encode.fst"
let _78_828 = (encode_term v2 env)
in (match (_78_828) with
| (v2, decls2) -> begin
(let _162_619 = (FStar_SMTEncoding_Term.mk_LexCons v1 v2)
in (_162_619, (FStar_List.append decls1 decls2)))
end))
end))
end
| _78_830 -> begin
(
# 576 "FStar.SMTEncoding.Encode.fst"
let _78_833 = (encode_args args_e env)
in (match (_78_833) with
| (args, decls) -> begin
(
# 578 "FStar.SMTEncoding.Encode.fst"
let encode_partial_app = (fun ht_opt -> (
# 579 "FStar.SMTEncoding.Encode.fst"
let _78_838 = (encode_term head env)
in (match (_78_838) with
| (head, decls') -> begin
(
# 580 "FStar.SMTEncoding.Encode.fst"
let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(
# 584 "FStar.SMTEncoding.Encode.fst"
let _78_847 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_78_847) with
| (formals, rest) -> begin
(
# 585 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _78_851 _78_855 -> (match ((_78_851, _78_855)) with
| ((bv, _78_850), (a, _78_854)) -> begin
FStar_Syntax_Syntax.NT ((bv, a))
end)) formals args_e)
in (
# 586 "FStar.SMTEncoding.Encode.fst"
let ty = (let _162_624 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right _162_624 (FStar_Syntax_Subst.subst subst)))
in (
# 587 "FStar.SMTEncoding.Encode.fst"
let _78_860 = (encode_term_pred None ty env app_tm)
in (match (_78_860) with
| (has_type, decls'') -> begin
(
# 588 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (
# 589 "FStar.SMTEncoding.Encode.fst"
let e_typing = (let _162_626 = (let _162_625 = (FStar_SMTEncoding_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_162_625, None))
in FStar_SMTEncoding_Term.Assume (_162_626))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (
# 593 "FStar.SMTEncoding.Encode.fst"
let encode_full_app = (fun fv -> (
# 594 "FStar.SMTEncoding.Encode.fst"
let _78_867 = (lookup_free_var_sym env fv)
in (match (_78_867) with
| (fname, fuel_args) -> begin
(
# 595 "FStar.SMTEncoding.Encode.fst"
let tm = (FStar_SMTEncoding_Term.mkApp' (fname, (FStar_List.append fuel_args args)))
in (tm, decls))
end)))
in (
# 598 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Subst.compress head)
in (
# 600 "FStar.SMTEncoding.Encode.fst"
let head_type = (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
Some (x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(let _162_630 = (let _162_629 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right _162_629 Prims.snd))
in Some (_162_630))
end
| FStar_Syntax_Syntax.Tm_ascribed (_78_899, t, _78_902) -> begin
Some (t)
end
| _78_906 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(
# 611 "FStar.SMTEncoding.Encode.fst"
let head_type = (let _162_631 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine _162_631))
in (
# 612 "FStar.SMTEncoding.Encode.fst"
let _78_914 = (curried_arrow_formals_comp head_type)
in (match (_78_914) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| _78_930 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some ((formals, c))))
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
# 626 "FStar.SMTEncoding.Encode.fst"
let _78_939 = (FStar_Syntax_Subst.open_term' bs body)
in (match (_78_939) with
| (bs, body, opening) -> begin
(
# 627 "FStar.SMTEncoding.Encode.fst"
let fallback = (fun _78_941 -> (match (()) with
| () -> begin
(
# 628 "FStar.SMTEncoding.Encode.fst"
let f = (varops.fresh "Tm_abs")
in (
# 629 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.DeclFun ((f, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _162_634 = (FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
in (_162_634, (decl)::[]))))
end))
in (match (lopt) with
| None -> begin
(
# 634 "FStar.SMTEncoding.Encode.fst"
let _78_945 = (let _162_636 = (let _162_635 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s" _162_635))
in (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos _162_636))
in (fallback ()))
end
| Some (lc) -> begin
if (let _162_637 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (FStar_All.pipe_left Prims.op_Negation _162_637)) then begin
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
let _78_957 = (encode_binders None bs env)
in (match (_78_957) with
| (vars, guards, envbody, decls, _78_956) -> begin
(
# 645 "FStar.SMTEncoding.Encode.fst"
let _78_960 = (encode_term body envbody)
in (match (_78_960) with
| (body, decls') -> begin
(
# 646 "FStar.SMTEncoding.Encode.fst"
let key_body = (let _162_641 = (let _162_640 = (let _162_639 = (let _162_638 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_162_638, body))
in (FStar_SMTEncoding_Term.mkImp _162_639))
in ([], vars, _162_640))
in (FStar_SMTEncoding_Term.mkForall _162_641))
in (
# 647 "FStar.SMTEncoding.Encode.fst"
let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (
# 648 "FStar.SMTEncoding.Encode.fst"
let tkey = (FStar_SMTEncoding_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_SMTEncoding_Term.hash)) with
| Some (t, _78_966, _78_968) -> begin
(let _162_644 = (let _162_643 = (let _162_642 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (t, _162_642))
in (FStar_SMTEncoding_Term.mkApp _162_643))
in (_162_644, []))
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
let f = (let _162_646 = (let _162_645 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV cvars)
in (fsym, _162_645))
in (FStar_SMTEncoding_Term.mkApp _162_646))
in (
# 661 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply f vars)
in (
# 662 "FStar.SMTEncoding.Encode.fst"
let tfun = (FStar_Syntax_Util.arrow bs c)
in (
# 663 "FStar.SMTEncoding.Encode.fst"
let _78_983 = (encode_term_pred None tfun env f)
in (match (_78_983) with
| (f_has_t, decls'') -> begin
(
# 664 "FStar.SMTEncoding.Encode.fst"
let typing_f = (let _162_648 = (let _162_647 = (FStar_SMTEncoding_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_162_647, Some ((Prims.strcat fsym " typing"))))
in FStar_SMTEncoding_Term.Assume (_162_648))
in (
# 666 "FStar.SMTEncoding.Encode.fst"
let interp_f = (let _162_655 = (let _162_654 = (let _162_653 = (let _162_652 = (let _162_651 = (let _162_650 = (FStar_SMTEncoding_Term.mk_IsTyped app)
in (let _162_649 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_162_650, _162_649)))
in (FStar_SMTEncoding_Term.mkImp _162_651))
in (((app)::[])::[], (FStar_List.append vars cvars), _162_652))
in (FStar_SMTEncoding_Term.mkForall _162_653))
in (_162_654, Some ((Prims.strcat fsym " interpretation"))))
in FStar_SMTEncoding_Term.Assume (_162_655))
in (
# 668 "FStar.SMTEncoding.Encode.fst"
let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (
# 669 "FStar.SMTEncoding.Encode.fst"
let _78_987 = (FStar_Util.smap_add env.cache tkey.FStar_SMTEncoding_Term.hash (fsym, cvar_sorts, f_decls))
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
| FStar_Syntax_Syntax.Tm_let ((_78_990, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (_78_1002); FStar_Syntax_Syntax.lbunivs = _78_1000; FStar_Syntax_Syntax.lbtyp = _78_998; FStar_Syntax_Syntax.lbeff = _78_996; FStar_Syntax_Syntax.lbdef = _78_994}::_78_992), _78_1008) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _78_1017; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _78_1014; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (_78_1027) -> begin
(
# 682 "FStar.SMTEncoding.Encode.fst"
let _78_1029 = (FStar_TypeChecker_Errors.warn t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (
# 683 "FStar.SMTEncoding.Encode.fst"
let e = (varops.fresh "let-rec")
in (
# 684 "FStar.SMTEncoding.Encode.fst"
let decl_e = FStar_SMTEncoding_Term.DeclFun ((e, [], FStar_SMTEncoding_Term.Term_sort, None))
in (let _162_656 = (FStar_SMTEncoding_Term.mkFreeV (e, FStar_SMTEncoding_Term.Term_sort))
in (_162_656, (decl_e)::[])))))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end))))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (
# 691 "FStar.SMTEncoding.Encode.fst"
let _78_1045 = (encode_term e1 env)
in (match (_78_1045) with
| (ee1, decls1) -> begin
(
# 692 "FStar.SMTEncoding.Encode.fst"
let _78_1048 = (FStar_Syntax_Subst.open_term (((x, None))::[]) e2)
in (match (_78_1048) with
| (xs, e2) -> begin
(
# 693 "FStar.SMTEncoding.Encode.fst"
let _78_1052 = (FStar_List.hd xs)
in (match (_78_1052) with
| (x, _78_1051) -> begin
(
# 694 "FStar.SMTEncoding.Encode.fst"
let env' = (push_term_var env x ee1)
in (
# 695 "FStar.SMTEncoding.Encode.fst"
let _78_1056 = (encode_body e2 env')
in (match (_78_1056) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (
# 699 "FStar.SMTEncoding.Encode.fst"
let _78_1064 = (encode_term e env)
in (match (_78_1064) with
| (scr, decls) -> begin
(
# 700 "FStar.SMTEncoding.Encode.fst"
let _78_1101 = (FStar_List.fold_right (fun b _78_1068 -> (match (_78_1068) with
| (else_case, decls) -> begin
(
# 701 "FStar.SMTEncoding.Encode.fst"
let _78_1072 = (FStar_Syntax_Subst.open_branch b)
in (match (_78_1072) with
| (p, w, br) -> begin
(
# 702 "FStar.SMTEncoding.Encode.fst"
let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _78_1076 _78_1079 -> (match ((_78_1076, _78_1079)) with
| ((env0, pattern), (else_case, decls)) -> begin
(
# 704 "FStar.SMTEncoding.Encode.fst"
let guard = (pattern.guard scr)
in (
# 705 "FStar.SMTEncoding.Encode.fst"
let projections = (pattern.projections scr)
in (
# 706 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _78_1085 -> (match (_78_1085) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (
# 707 "FStar.SMTEncoding.Encode.fst"
let _78_1095 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(
# 710 "FStar.SMTEncoding.Encode.fst"
let _78_1092 = (encode_term w env)
in (match (_78_1092) with
| (w, decls2) -> begin
(let _162_690 = (let _162_689 = (let _162_688 = (let _162_687 = (let _162_686 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Term.mkTrue)
in (w, _162_686))
in (FStar_SMTEncoding_Term.mkEq _162_687))
in (guard, _162_688))
in (FStar_SMTEncoding_Term.mkAnd _162_689))
in (_162_690, decls2))
end))
end)
in (match (_78_1095) with
| (guard, decls2) -> begin
(
# 712 "FStar.SMTEncoding.Encode.fst"
let _78_1098 = (encode_br br env)
in (match (_78_1098) with
| (br, decls3) -> begin
(let _162_691 = (FStar_SMTEncoding_Term.mkITE (guard, br, else_case))
in (_162_691, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end))
end)) pats (default_case, decls))
in (match (_78_1101) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _78_1107 -> begin
(let _162_694 = (encode_one_pat env pat)
in (_162_694)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (
# 726 "FStar.SMTEncoding.Encode.fst"
let _78_1110 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _162_697 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _162_697))
end else begin
()
end
in (
# 727 "FStar.SMTEncoding.Encode.fst"
let _78_1114 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (_78_1114) with
| (vars, pat_term) -> begin
(
# 729 "FStar.SMTEncoding.Encode.fst"
let _78_1126 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _78_1117 v -> (match (_78_1117) with
| (env, vars) -> begin
(
# 730 "FStar.SMTEncoding.Encode.fst"
let _78_1123 = (gen_term_var env v)
in (match (_78_1123) with
| (xx, _78_1121, env) -> begin
(env, ((v, (xx, FStar_SMTEncoding_Term.Term_sort)))::vars)
end))
end)) (env, [])))
in (match (_78_1126) with
| (env, vars) -> begin
(
# 733 "FStar.SMTEncoding.Encode.fst"
let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_78_1131) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Term.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(let _162_705 = (let _162_704 = (encode_const c)
in (scrutinee, _162_704))
in (FStar_SMTEncoding_Term.mkEq _162_705))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(
# 741 "FStar.SMTEncoding.Encode.fst"
let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (
# 742 "FStar.SMTEncoding.Encode.fst"
let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _78_1153 -> (match (_78_1153) with
| (arg, _78_1152) -> begin
(
# 743 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _162_708 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _162_708)))
end))))
in (FStar_SMTEncoding_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (
# 747 "FStar.SMTEncoding.Encode.fst"
let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (_78_1160) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
((x, scrutinee))::[]
end
| FStar_Syntax_Syntax.Pat_constant (_78_1170) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(let _162_716 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _78_1180 -> (match (_78_1180) with
| (arg, _78_1179) -> begin
(
# 759 "FStar.SMTEncoding.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (let _162_715 = (FStar_SMTEncoding_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _162_715)))
end))))
in (FStar_All.pipe_right _162_716 FStar_List.flatten))
end))
in (
# 763 "FStar.SMTEncoding.Encode.fst"
let pat_term = (fun _78_1183 -> (match (()) with
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
let _78_1199 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _78_1189 _78_1193 -> (match ((_78_1189, _78_1193)) with
| ((tms, decls), (t, _78_1192)) -> begin
(
# 776 "FStar.SMTEncoding.Encode.fst"
let _78_1196 = (encode_term t env)
in (match (_78_1196) with
| (t, decls') -> begin
((t)::tms, (FStar_List.append decls decls'))
end))
end)) ([], [])))
in (match (_78_1199) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (
# 781 "FStar.SMTEncoding.Encode.fst"
let _78_1205 = (encode_formula_with_labels phi env)
in (match (_78_1205) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _78_1208 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (
# 788 "FStar.SMTEncoding.Encode.fst"
let rec list_elements = (fun e -> (
# 789 "FStar.SMTEncoding.Encode.fst"
let _78_1217 = (let _162_731 = (FStar_Syntax_Util.unmeta e)
in (FStar_Syntax_Util.head_and_args _162_731))
in (match (_78_1217) with
| (head, args) -> begin
(match ((let _162_733 = (let _162_732 = (FStar_Syntax_Util.un_uinst head)
in _162_732.FStar_Syntax_Syntax.n)
in (_162_733, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _78_1221) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
[]
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _78_1234::(hd, _78_1231)::(tl, _78_1227)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid) -> begin
(let _162_734 = (list_elements tl)
in (hd)::_162_734)
end
| _78_1238 -> begin
(
# 794 "FStar.SMTEncoding.Encode.fst"
let _78_1239 = (FStar_TypeChecker_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end)
end)))
in (
# 796 "FStar.SMTEncoding.Encode.fst"
let one_pat = (fun p -> (
# 797 "FStar.SMTEncoding.Encode.fst"
let _78_1245 = (let _162_737 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right _162_737 FStar_Syntax_Util.head_and_args))
in (match (_78_1245) with
| (head, args) -> begin
(match ((let _162_739 = (let _162_738 = (FStar_Syntax_Util.un_uinst head)
in _162_738.FStar_Syntax_Syntax.n)
in (_162_739, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (_78_1253, _78_1255)::(e, _78_1250)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
(e, None)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (e, _78_1263)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
(e, None)
end
| _78_1268 -> begin
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
let _78_1276 = (let _162_744 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right _162_744 FStar_Syntax_Util.head_and_args))
in (match (_78_1276) with
| (head, args) -> begin
(match ((let _162_746 = (let _162_745 = (FStar_Syntax_Util.un_uinst head)
in _162_745.FStar_Syntax_Syntax.n)
in (_162_746, args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (e, _78_1281)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| _78_1286 -> begin
None
end)
end)))
in (match (elts) with
| t::[] -> begin
(match ((smt_pat_or t)) with
| Some (e) -> begin
(let _162_749 = (list_elements e)
in (FStar_All.pipe_right _162_749 (FStar_List.map (fun branch -> (let _162_748 = (list_elements branch)
in (FStar_All.pipe_right _162_748 (FStar_List.map one_pat)))))))
end
| _78_1293 -> begin
(let _162_750 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_162_750)::[])
end)
end
| _78_1295 -> begin
(let _162_751 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (_162_751)::[])
end))))
in (
# 820 "FStar.SMTEncoding.Encode.fst"
let _78_1329 = (match ((let _162_752 = (FStar_Syntax_Subst.compress t)
in _162_752.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(
# 822 "FStar.SMTEncoding.Encode.fst"
let _78_1302 = (FStar_Syntax_Subst.open_comp binders c)
in (match (_78_1302) with
| (binders, c) -> begin
(
# 823 "FStar.SMTEncoding.Encode.fst"
let ct = (FStar_Syntax_Util.comp_to_comp_typ c)
in (match (ct.FStar_Syntax_Syntax.effect_args) with
| (pre, _78_1314)::(post, _78_1310)::(pats, _78_1306)::[] -> begin
(
# 826 "FStar.SMTEncoding.Encode.fst"
let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _162_753 = (lemma_pats pats')
in (binders, pre, post, _162_753)))
end
| _78_1322 -> begin
(FStar_All.failwith "impos")
end))
end))
end
| _78_1324 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_78_1329) with
| (binders, pre, post, patterns) -> begin
(
# 834 "FStar.SMTEncoding.Encode.fst"
let _78_1336 = (encode_binders None binders env)
in (match (_78_1336) with
| (vars, guards, env, decls, _78_1335) -> begin
(
# 837 "FStar.SMTEncoding.Encode.fst"
let _78_1349 = (let _162_757 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (
# 838 "FStar.SMTEncoding.Encode.fst"
let _78_1346 = (let _162_756 = (FStar_All.pipe_right branch (FStar_List.map (fun _78_1341 -> (match (_78_1341) with
| (t, _78_1340) -> begin
(encode_term t (
# 838 "FStar.SMTEncoding.Encode.fst"
let _78_1342 = env
in {bindings = _78_1342.bindings; depth = _78_1342.depth; tcenv = _78_1342.tcenv; warn = _78_1342.warn; cache = _78_1342.cache; nolabels = _78_1342.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _78_1342.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _162_756 FStar_List.unzip))
in (match (_78_1346) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _162_757 FStar_List.unzip))
in (match (_78_1349) with
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _162_760 = (let _162_759 = (FStar_SMTEncoding_Term.mkFreeV l)
in (FStar_SMTEncoding_Term.mk_Precedes _162_759 e))
in (_162_760)::p))))
end
| _78_1359 -> begin
(
# 851 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _162_766 = (FStar_SMTEncoding_Term.mk_Precedes tl e)
in (_162_766)::p))))
end
| (x, FStar_SMTEncoding_Term.Term_sort)::vars -> begin
(let _162_768 = (let _162_767 = (FStar_SMTEncoding_Term.mkFreeV (x, FStar_SMTEncoding_Term.Term_sort))
in (FStar_SMTEncoding_Term.mk_LexCons _162_767 tl))
in (aux _162_768 vars))
end
| _78_1371 -> begin
pats
end))
in (let _162_769 = (FStar_SMTEncoding_Term.mkFreeV ("Prims.LexTop", FStar_SMTEncoding_Term.Term_sort))
in (aux _162_769 vars)))
end)
end)
in (
# 858 "FStar.SMTEncoding.Encode.fst"
let env = (
# 858 "FStar.SMTEncoding.Encode.fst"
let _78_1373 = env
in {bindings = _78_1373.bindings; depth = _78_1373.depth; tcenv = _78_1373.tcenv; warn = _78_1373.warn; cache = _78_1373.cache; nolabels = true; use_zfuel_name = _78_1373.use_zfuel_name; encode_non_total_function_typ = _78_1373.encode_non_total_function_typ})
in (
# 859 "FStar.SMTEncoding.Encode.fst"
let _78_1378 = (let _162_770 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula _162_770 env))
in (match (_78_1378) with
| (pre, decls'') -> begin
(
# 860 "FStar.SMTEncoding.Encode.fst"
let _78_1381 = (let _162_771 = (FStar_Syntax_Util.unmeta post)
in (encode_formula _162_771 env))
in (match (_78_1381) with
| (post, decls''') -> begin
(
# 861 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _162_776 = (let _162_775 = (let _162_774 = (let _162_773 = (let _162_772 = (FStar_SMTEncoding_Term.mk_and_l ((pre)::guards))
in (_162_772, post))
in (FStar_SMTEncoding_Term.mkImp _162_773))
in (pats, vars, _162_774))
in (FStar_SMTEncoding_Term.mkForall _162_775))
in (_162_776, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula_with_labels : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * labels * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (
# 865 "FStar.SMTEncoding.Encode.fst"
let enc = (fun f l -> (
# 866 "FStar.SMTEncoding.Encode.fst"
let _78_1395 = (FStar_Util.fold_map (fun decls x -> (
# 866 "FStar.SMTEncoding.Encode.fst"
let _78_1392 = (encode_term (Prims.fst x) env)
in (match (_78_1392) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))) [] l)
in (match (_78_1395) with
| (decls, args) -> begin
(let _162_794 = (f args)
in (_162_794, [], decls))
end)))
in (
# 869 "FStar.SMTEncoding.Encode.fst"
let const_op = (fun f _78_1398 -> (f, [], []))
in (
# 870 "FStar.SMTEncoding.Encode.fst"
let un_op = (fun f l -> (let _162_808 = (FStar_List.hd l)
in (FStar_All.pipe_left f _162_808)))
in (
# 871 "FStar.SMTEncoding.Encode.fst"
let bin_op = (fun f _78_8 -> (match (_78_8) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _78_1409 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 875 "FStar.SMTEncoding.Encode.fst"
let enc_prop_c = (fun f l -> (
# 876 "FStar.SMTEncoding.Encode.fst"
let _78_1429 = (FStar_List.fold_right (fun _78_1417 _78_1421 -> (match ((_78_1417, _78_1421)) with
| ((t, _78_1416), (phis, labs, decls)) -> begin
(
# 878 "FStar.SMTEncoding.Encode.fst"
let _78_1425 = (encode_formula_with_labels t env)
in (match (_78_1425) with
| (phi, labs', decls') -> begin
((phi)::phis, (FStar_List.append labs' labs), (FStar_List.append decls' decls))
end))
end)) l ([], [], []))
in (match (_78_1429) with
| (phis, labs, decls) -> begin
(let _162_833 = (f phis)
in (_162_833, labs, decls))
end)))
in (
# 883 "FStar.SMTEncoding.Encode.fst"
let eq_op = (fun _78_9 -> (match (_78_9) with
| _78_1436::_78_1434::e1::e2::[] -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_SMTEncoding_Term.mkEq) l)
end))
in (
# 887 "FStar.SMTEncoding.Encode.fst"
let mk_imp = (fun _78_10 -> (match (_78_10) with
| (lhs, _78_1447)::(rhs, _78_1443)::[] -> begin
(
# 889 "FStar.SMTEncoding.Encode.fst"
let _78_1453 = (encode_formula_with_labels rhs env)
in (match (_78_1453) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _78_1456) -> begin
(l1, labs1, decls1)
end
| _78_1460 -> begin
(
# 893 "FStar.SMTEncoding.Encode.fst"
let _78_1464 = (encode_formula_with_labels lhs env)
in (match (_78_1464) with
| (l2, labs2, decls2) -> begin
(let _162_838 = (FStar_SMTEncoding_Term.mkImp (l2, l1))
in (_162_838, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _78_1466 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 898 "FStar.SMTEncoding.Encode.fst"
let mk_ite = (fun _78_11 -> (match (_78_11) with
| (guard, _78_1479)::(_then, _78_1475)::(_else, _78_1471)::[] -> begin
(
# 900 "FStar.SMTEncoding.Encode.fst"
let _78_1485 = (encode_formula_with_labels guard env)
in (match (_78_1485) with
| (g, labs1, decls1) -> begin
(
# 901 "FStar.SMTEncoding.Encode.fst"
let _78_1489 = (encode_formula_with_labels _then env)
in (match (_78_1489) with
| (t, labs2, decls2) -> begin
(
# 902 "FStar.SMTEncoding.Encode.fst"
let _78_1493 = (encode_formula_with_labels _else env)
in (match (_78_1493) with
| (e, labs3, decls3) -> begin
(
# 903 "FStar.SMTEncoding.Encode.fst"
let res = (FStar_SMTEncoding_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append labs1 labs2) labs3), (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _78_1496 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 908 "FStar.SMTEncoding.Encode.fst"
let unboxInt_l = (fun f l -> (let _162_850 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f _162_850)))
in (
# 909 "FStar.SMTEncoding.Encode.fst"
let connectives = (let _162_903 = (let _162_859 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkAnd))
in (FStar_Syntax_Const.and_lid, _162_859))
in (let _162_902 = (let _162_901 = (let _162_865 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkOr))
in (FStar_Syntax_Const.or_lid, _162_865))
in (let _162_900 = (let _162_899 = (let _162_898 = (let _162_874 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Term.mkIff))
in (FStar_Syntax_Const.iff_lid, _162_874))
in (let _162_897 = (let _162_896 = (let _162_895 = (let _162_883 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Term.mkNot))
in (FStar_Syntax_Const.not_lid, _162_883))
in (_162_895)::((FStar_Syntax_Const.eq2_lid, eq_op))::((FStar_Syntax_Const.true_lid, (const_op FStar_SMTEncoding_Term.mkTrue)))::((FStar_Syntax_Const.false_lid, (const_op FStar_SMTEncoding_Term.mkFalse)))::[])
in ((FStar_Syntax_Const.ite_lid, mk_ite))::_162_896)
in (_162_898)::_162_897))
in ((FStar_Syntax_Const.imp_lid, mk_imp))::_162_899)
in (_162_901)::_162_900))
in (_162_903)::_162_902))
in (
# 921 "FStar.SMTEncoding.Encode.fst"
let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(
# 923 "FStar.SMTEncoding.Encode.fst"
let _78_1515 = (encode_formula_with_labels phi' env)
in (match (_78_1515) with
| (phi, labs, decls) -> begin
(let _162_906 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled ((phi, msg, r))))
in (_162_906, [], decls))
end))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(
# 927 "FStar.SMTEncoding.Encode.fst"
let _78_1522 = (encode_match e pats FStar_SMTEncoding_Term.mkFalse env encode_formula)
in (match (_78_1522) with
| (t, decls) -> begin
(t, [], decls)
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = _78_1529; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = _78_1526; FStar_Syntax_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 931 "FStar.SMTEncoding.Encode.fst"
let _78_1540 = (encode_let x t1 e1 e2 env encode_formula)
in (match (_78_1540) with
| (t, decls) -> begin
(t, [], decls)
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(
# 935 "FStar.SMTEncoding.Encode.fst"
let head = (FStar_Syntax_Util.un_uinst head)
in (match ((head.FStar_Syntax_Syntax.n, args)) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), _78_1557::(x, _78_1554)::(t, _78_1550)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(
# 938 "FStar.SMTEncoding.Encode.fst"
let _78_1562 = (encode_term x env)
in (match (_78_1562) with
| (x, decls) -> begin
(
# 939 "FStar.SMTEncoding.Encode.fst"
let _78_1565 = (encode_term t env)
in (match (_78_1565) with
| (t, decls') -> begin
(let _162_907 = (FStar_SMTEncoding_Term.mk_HasType x t)
in (_162_907, [], (FStar_List.append decls decls')))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), _78_1583::_78_1581::(r, _78_1578)::(msg, _78_1574)::(phi, _78_1570)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(match ((let _162_911 = (let _162_908 = (FStar_Syntax_Subst.compress r)
in _162_908.FStar_Syntax_Syntax.n)
in (let _162_910 = (let _162_909 = (FStar_Syntax_Subst.compress msg)
in _162_909.FStar_Syntax_Syntax.n)
in (_162_911, _162_910)))) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, _78_1591))) -> begin
(
# 945 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((phi, FStar_Syntax_Syntax.Meta_labeled (((FStar_Util.string_of_unicode s), r, false))))) None r)
in (fallback phi))
end
| _78_1598 -> begin
(fallback phi)
end)
end
| _78_1600 -> begin
(
# 952 "FStar.SMTEncoding.Encode.fst"
let _78_1603 = (encode_term phi env)
in (match (_78_1603) with
| (tt, decls) -> begin
(let _162_912 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_162_912, [], decls))
end))
end))
end
| _78_1605 -> begin
(
# 957 "FStar.SMTEncoding.Encode.fst"
let _78_1608 = (encode_term phi env)
in (match (_78_1608) with
| (tt, decls) -> begin
(let _162_913 = (FStar_SMTEncoding_Term.mk_Valid tt)
in (_162_913, [], decls))
end))
end))
in (
# 960 "FStar.SMTEncoding.Encode.fst"
let encode_q_body = (fun env bs ps body -> (
# 961 "FStar.SMTEncoding.Encode.fst"
let _78_1620 = (encode_binders None bs env)
in (match (_78_1620) with
| (vars, guards, env, decls, _78_1619) -> begin
(
# 962 "FStar.SMTEncoding.Encode.fst"
let _78_1633 = (let _162_925 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (
# 963 "FStar.SMTEncoding.Encode.fst"
let _78_1630 = (let _162_924 = (FStar_All.pipe_right p (FStar_List.map (fun _78_1625 -> (match (_78_1625) with
| (t, _78_1624) -> begin
(encode_term t (
# 963 "FStar.SMTEncoding.Encode.fst"
let _78_1626 = env
in {bindings = _78_1626.bindings; depth = _78_1626.depth; tcenv = _78_1626.tcenv; warn = _78_1626.warn; cache = _78_1626.cache; nolabels = _78_1626.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _78_1626.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _162_924 FStar_List.unzip))
in (match (_78_1630) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _162_925 FStar_List.unzip))
in (match (_78_1633) with
| (pats, decls') -> begin
(
# 965 "FStar.SMTEncoding.Encode.fst"
let _78_1637 = (encode_formula_with_labels body env)
in (match (_78_1637) with
| (body, labs, decls'') -> begin
(let _162_926 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (vars, pats, _162_926, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (
# 968 "FStar.SMTEncoding.Encode.fst"
let _78_1638 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _162_927 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print1 ">>>> Destructing as formula ... %s\n" _162_927))
end else begin
()
end
in (
# 970 "FStar.SMTEncoding.Encode.fst"
let phi = (FStar_Syntax_Util.unascribe phi)
in (match ((FStar_Syntax_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _78_1650 -> (match (_78_1650) with
| (l, _78_1649) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_78_1653, f) -> begin
(f arms)
end)
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
(
# 980 "FStar.SMTEncoding.Encode.fst"
let _78_1663 = if (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low) then begin
(let _162_944 = (FStar_All.pipe_right vars (FStar_Syntax_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _162_944))
end else begin
()
end
in (
# 983 "FStar.SMTEncoding.Encode.fst"
let _78_1671 = (encode_q_body env vars pats body)
in (match (_78_1671) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _162_947 = (let _162_946 = (let _162_945 = (FStar_SMTEncoding_Term.mkImp (guard, body))
in (pats, vars, _162_945))
in (FStar_SMTEncoding_Term.mkForall _162_946))
in (_162_947, labs, decls))
end)))
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
(
# 987 "FStar.SMTEncoding.Encode.fst"
let _78_1684 = (encode_q_body env vars pats body)
in (match (_78_1684) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _162_950 = (let _162_949 = (let _162_948 = (FStar_SMTEncoding_Term.mkAnd (guard, body))
in (pats, vars, _162_948))
in (FStar_SMTEncoding_Term.mkExists _162_949))
in (_162_950, labs, decls))
end))
end))))))))))))))))

# 996 "FStar.SMTEncoding.Encode.fst"
type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}

# 996 "FStar.SMTEncoding.Encode.fst"
let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))

# 1002 "FStar.SMTEncoding.Encode.fst"
let prims : prims_t = (
# 1003 "FStar.SMTEncoding.Encode.fst"
let _78_1690 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (_78_1690) with
| (asym, a) -> begin
(
# 1004 "FStar.SMTEncoding.Encode.fst"
let _78_1693 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_78_1693) with
| (xsym, x) -> begin
(
# 1005 "FStar.SMTEncoding.Encode.fst"
let _78_1696 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (_78_1696) with
| (ysym, y) -> begin
(
# 1006 "FStar.SMTEncoding.Encode.fst"
let deffun = (fun vars body x -> (FStar_SMTEncoding_Term.DefineFun ((x, vars, FStar_SMTEncoding_Term.Term_sort, body, None)))::[])
in (
# 1007 "FStar.SMTEncoding.Encode.fst"
let quant = (fun vars body x -> (
# 1008 "FStar.SMTEncoding.Encode.fst"
let t1 = (let _162_993 = (let _162_992 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (x, _162_992))
in (FStar_SMTEncoding_Term.mkApp _162_993))
in (
# 1009 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _162_995 = (let _162_994 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _162_994, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_162_995))
in (let _162_1001 = (let _162_1000 = (let _162_999 = (let _162_998 = (let _162_997 = (let _162_996 = (FStar_SMTEncoding_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _162_996))
in (FStar_SMTEncoding_Term.mkForall _162_997))
in (_162_998, None))
in FStar_SMTEncoding_Term.Assume (_162_999))
in (_162_1000)::[])
in (vname_decl)::_162_1001))))
in (
# 1012 "FStar.SMTEncoding.Encode.fst"
let axy = ((asym, FStar_SMTEncoding_Term.Term_sort))::((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1013 "FStar.SMTEncoding.Encode.fst"
let xy = ((xsym, FStar_SMTEncoding_Term.Term_sort))::((ysym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1014 "FStar.SMTEncoding.Encode.fst"
let qx = ((xsym, FStar_SMTEncoding_Term.Term_sort))::[]
in (
# 1015 "FStar.SMTEncoding.Encode.fst"
let prims = (let _162_1161 = (let _162_1010 = (let _162_1009 = (let _162_1008 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1008))
in (quant axy _162_1009))
in (FStar_Syntax_Const.op_Eq, _162_1010))
in (let _162_1160 = (let _162_1159 = (let _162_1017 = (let _162_1016 = (let _162_1015 = (let _162_1014 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (FStar_SMTEncoding_Term.mkNot _162_1014))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1015))
in (quant axy _162_1016))
in (FStar_Syntax_Const.op_notEq, _162_1017))
in (let _162_1158 = (let _162_1157 = (let _162_1026 = (let _162_1025 = (let _162_1024 = (let _162_1023 = (let _162_1022 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1021 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1022, _162_1021)))
in (FStar_SMTEncoding_Term.mkLT _162_1023))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1024))
in (quant xy _162_1025))
in (FStar_Syntax_Const.op_LT, _162_1026))
in (let _162_1156 = (let _162_1155 = (let _162_1035 = (let _162_1034 = (let _162_1033 = (let _162_1032 = (let _162_1031 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1030 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1031, _162_1030)))
in (FStar_SMTEncoding_Term.mkLTE _162_1032))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1033))
in (quant xy _162_1034))
in (FStar_Syntax_Const.op_LTE, _162_1035))
in (let _162_1154 = (let _162_1153 = (let _162_1044 = (let _162_1043 = (let _162_1042 = (let _162_1041 = (let _162_1040 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1039 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1040, _162_1039)))
in (FStar_SMTEncoding_Term.mkGT _162_1041))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1042))
in (quant xy _162_1043))
in (FStar_Syntax_Const.op_GT, _162_1044))
in (let _162_1152 = (let _162_1151 = (let _162_1053 = (let _162_1052 = (let _162_1051 = (let _162_1050 = (let _162_1049 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1048 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1049, _162_1048)))
in (FStar_SMTEncoding_Term.mkGTE _162_1050))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1051))
in (quant xy _162_1052))
in (FStar_Syntax_Const.op_GTE, _162_1053))
in (let _162_1150 = (let _162_1149 = (let _162_1062 = (let _162_1061 = (let _162_1060 = (let _162_1059 = (let _162_1058 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1057 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1058, _162_1057)))
in (FStar_SMTEncoding_Term.mkSub _162_1059))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _162_1060))
in (quant xy _162_1061))
in (FStar_Syntax_Const.op_Subtraction, _162_1062))
in (let _162_1148 = (let _162_1147 = (let _162_1069 = (let _162_1068 = (let _162_1067 = (let _162_1066 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Term.mkMinus _162_1066))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _162_1067))
in (quant qx _162_1068))
in (FStar_Syntax_Const.op_Minus, _162_1069))
in (let _162_1146 = (let _162_1145 = (let _162_1078 = (let _162_1077 = (let _162_1076 = (let _162_1075 = (let _162_1074 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1073 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1074, _162_1073)))
in (FStar_SMTEncoding_Term.mkAdd _162_1075))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _162_1076))
in (quant xy _162_1077))
in (FStar_Syntax_Const.op_Addition, _162_1078))
in (let _162_1144 = (let _162_1143 = (let _162_1087 = (let _162_1086 = (let _162_1085 = (let _162_1084 = (let _162_1083 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1082 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1083, _162_1082)))
in (FStar_SMTEncoding_Term.mkMul _162_1084))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _162_1085))
in (quant xy _162_1086))
in (FStar_Syntax_Const.op_Multiply, _162_1087))
in (let _162_1142 = (let _162_1141 = (let _162_1096 = (let _162_1095 = (let _162_1094 = (let _162_1093 = (let _162_1092 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1091 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1092, _162_1091)))
in (FStar_SMTEncoding_Term.mkDiv _162_1093))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _162_1094))
in (quant xy _162_1095))
in (FStar_Syntax_Const.op_Division, _162_1096))
in (let _162_1140 = (let _162_1139 = (let _162_1105 = (let _162_1104 = (let _162_1103 = (let _162_1102 = (let _162_1101 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1100 = (FStar_SMTEncoding_Term.unboxInt y)
in (_162_1101, _162_1100)))
in (FStar_SMTEncoding_Term.mkMod _162_1102))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt _162_1103))
in (quant xy _162_1104))
in (FStar_Syntax_Const.op_Modulus, _162_1105))
in (let _162_1138 = (let _162_1137 = (let _162_1114 = (let _162_1113 = (let _162_1112 = (let _162_1111 = (let _162_1110 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _162_1109 = (FStar_SMTEncoding_Term.unboxBool y)
in (_162_1110, _162_1109)))
in (FStar_SMTEncoding_Term.mkAnd _162_1111))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1112))
in (quant xy _162_1113))
in (FStar_Syntax_Const.op_And, _162_1114))
in (let _162_1136 = (let _162_1135 = (let _162_1123 = (let _162_1122 = (let _162_1121 = (let _162_1120 = (let _162_1119 = (FStar_SMTEncoding_Term.unboxBool x)
in (let _162_1118 = (FStar_SMTEncoding_Term.unboxBool y)
in (_162_1119, _162_1118)))
in (FStar_SMTEncoding_Term.mkOr _162_1120))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1121))
in (quant xy _162_1122))
in (FStar_Syntax_Const.op_Or, _162_1123))
in (let _162_1134 = (let _162_1133 = (let _162_1130 = (let _162_1129 = (let _162_1128 = (let _162_1127 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Term.mkNot _162_1127))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_1128))
in (quant qx _162_1129))
in (FStar_Syntax_Const.op_Negation, _162_1130))
in (_162_1133)::[])
in (_162_1135)::_162_1134))
in (_162_1137)::_162_1136))
in (_162_1139)::_162_1138))
in (_162_1141)::_162_1140))
in (_162_1143)::_162_1142))
in (_162_1145)::_162_1144))
in (_162_1147)::_162_1146))
in (_162_1149)::_162_1148))
in (_162_1151)::_162_1150))
in (_162_1153)::_162_1152))
in (_162_1155)::_162_1154))
in (_162_1157)::_162_1156))
in (_162_1159)::_162_1158))
in (_162_1161)::_162_1160))
in (
# 1032 "FStar.SMTEncoding.Encode.fst"
let mk = (fun l v -> (let _162_1193 = (FStar_All.pipe_right prims (FStar_List.filter (fun _78_1716 -> (match (_78_1716) with
| (l', _78_1715) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _162_1193 (FStar_List.collect (fun _78_1720 -> (match (_78_1720) with
| (_78_1718, b) -> begin
(b v)
end))))))
in (
# 1034 "FStar.SMTEncoding.Encode.fst"
let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _78_1726 -> (match (_78_1726) with
| (l', _78_1725) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is}))))))))
end))
end))
end))

# 1039 "FStar.SMTEncoding.Encode.fst"
let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (
# 1040 "FStar.SMTEncoding.Encode.fst"
let _78_1732 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_78_1732) with
| (xxsym, xx) -> begin
(
# 1041 "FStar.SMTEncoding.Encode.fst"
let _78_1735 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_78_1735) with
| (ffsym, ff) -> begin
(
# 1042 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (let _162_1219 = (let _162_1218 = (let _162_1217 = (let _162_1216 = (let _162_1215 = (let _162_1214 = (let _162_1213 = (let _162_1212 = (FStar_SMTEncoding_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _162_1212))
in (FStar_SMTEncoding_Term.mkEq _162_1213))
in (xx_has_type, _162_1214))
in (FStar_SMTEncoding_Term.mkImp _162_1215))
in (((xx_has_type)::[])::[], ((xxsym, FStar_SMTEncoding_Term.Term_sort))::((ffsym, FStar_SMTEncoding_Term.Fuel_sort))::vars, _162_1216))
in (FStar_SMTEncoding_Term.mkForall _162_1217))
in (_162_1218, Some ("pretyping")))
in FStar_SMTEncoding_Term.Assume (_162_1219)))
end))
end)))

# 1046 "FStar.SMTEncoding.Encode.fst"
let primitive_type_axioms : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (
# 1047 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1048 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1050 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1051 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1053 "FStar.SMTEncoding.Encode.fst"
let mk_unit = (fun env nm tt -> (
# 1054 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (let _162_1240 = (let _162_1231 = (let _162_1230 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in (_162_1230, Some ("unit typing")))
in FStar_SMTEncoding_Term.Assume (_162_1231))
in (let _162_1239 = (let _162_1238 = (let _162_1237 = (let _162_1236 = (let _162_1235 = (let _162_1234 = (let _162_1233 = (let _162_1232 = (FStar_SMTEncoding_Term.mkEq (x, FStar_SMTEncoding_Term.mk_Term_unit))
in (typing_pred, _162_1232))
in (FStar_SMTEncoding_Term.mkImp _162_1233))
in (((typing_pred)::[])::[], (xx)::[], _162_1234))
in (mkForall_fuel _162_1235))
in (_162_1236, Some ("unit inversion")))
in FStar_SMTEncoding_Term.Assume (_162_1237))
in (_162_1238)::[])
in (_162_1240)::_162_1239))))
in (
# 1057 "FStar.SMTEncoding.Encode.fst"
let mk_bool = (fun env nm tt -> (
# 1058 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1059 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)
in (
# 1060 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _162_1263 = (let _162_1252 = (let _162_1251 = (let _162_1250 = (let _162_1249 = (let _162_1248 = (let _162_1247 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in (typing_pred, _162_1247))
in (FStar_SMTEncoding_Term.mkImp _162_1248))
in (((typing_pred)::[])::[], (xx)::[], _162_1249))
in (mkForall_fuel _162_1250))
in (_162_1251, Some ("bool inversion")))
in FStar_SMTEncoding_Term.Assume (_162_1252))
in (let _162_1262 = (let _162_1261 = (let _162_1260 = (let _162_1259 = (let _162_1258 = (let _162_1257 = (let _162_1254 = (let _162_1253 = (FStar_SMTEncoding_Term.boxBool b)
in (_162_1253)::[])
in (_162_1254)::[])
in (let _162_1256 = (let _162_1255 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType _162_1255 tt))
in (_162_1257, (bb)::[], _162_1256)))
in (FStar_SMTEncoding_Term.mkForall _162_1258))
in (_162_1259, Some ("bool typing")))
in FStar_SMTEncoding_Term.Assume (_162_1260))
in (_162_1261)::[])
in (_162_1263)::_162_1262))))))
in (
# 1063 "FStar.SMTEncoding.Encode.fst"
let mk_int = (fun env nm tt -> (
# 1064 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1065 "FStar.SMTEncoding.Encode.fst"
let typing_pred_y = (FStar_SMTEncoding_Term.mk_HasType y tt)
in (
# 1066 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Int_sort)
in (
# 1067 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1068 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Int_sort)
in (
# 1069 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1070 "FStar.SMTEncoding.Encode.fst"
let precedes = (let _162_1277 = (let _162_1276 = (let _162_1275 = (let _162_1274 = (let _162_1273 = (let _162_1272 = (FStar_SMTEncoding_Term.boxInt a)
in (let _162_1271 = (let _162_1270 = (FStar_SMTEncoding_Term.boxInt b)
in (_162_1270)::[])
in (_162_1272)::_162_1271))
in (tt)::_162_1273)
in (tt)::_162_1274)
in ("Prims.Precedes", _162_1275))
in (FStar_SMTEncoding_Term.mkApp _162_1276))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _162_1277))
in (
# 1071 "FStar.SMTEncoding.Encode.fst"
let precedes_y_x = (let _162_1278 = (FStar_SMTEncoding_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid _162_1278))
in (let _162_1320 = (let _162_1284 = (let _162_1283 = (let _162_1282 = (let _162_1281 = (let _162_1280 = (let _162_1279 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in (typing_pred, _162_1279))
in (FStar_SMTEncoding_Term.mkImp _162_1280))
in (((typing_pred)::[])::[], (xx)::[], _162_1281))
in (mkForall_fuel _162_1282))
in (_162_1283, Some ("int inversion")))
in FStar_SMTEncoding_Term.Assume (_162_1284))
in (let _162_1319 = (let _162_1318 = (let _162_1292 = (let _162_1291 = (let _162_1290 = (let _162_1289 = (let _162_1286 = (let _162_1285 = (FStar_SMTEncoding_Term.boxInt b)
in (_162_1285)::[])
in (_162_1286)::[])
in (let _162_1288 = (let _162_1287 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType _162_1287 tt))
in (_162_1289, (bb)::[], _162_1288)))
in (FStar_SMTEncoding_Term.mkForall _162_1290))
in (_162_1291, Some ("int typing")))
in FStar_SMTEncoding_Term.Assume (_162_1292))
in (let _162_1317 = (let _162_1316 = (let _162_1315 = (let _162_1314 = (let _162_1313 = (let _162_1312 = (let _162_1311 = (let _162_1310 = (let _162_1309 = (let _162_1308 = (let _162_1307 = (let _162_1306 = (let _162_1295 = (let _162_1294 = (FStar_SMTEncoding_Term.unboxInt x)
in (let _162_1293 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_162_1294, _162_1293)))
in (FStar_SMTEncoding_Term.mkGT _162_1295))
in (let _162_1305 = (let _162_1304 = (let _162_1298 = (let _162_1297 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _162_1296 = (FStar_SMTEncoding_Term.mkInteger' 0)
in (_162_1297, _162_1296)))
in (FStar_SMTEncoding_Term.mkGTE _162_1298))
in (let _162_1303 = (let _162_1302 = (let _162_1301 = (let _162_1300 = (FStar_SMTEncoding_Term.unboxInt y)
in (let _162_1299 = (FStar_SMTEncoding_Term.unboxInt x)
in (_162_1300, _162_1299)))
in (FStar_SMTEncoding_Term.mkLT _162_1301))
in (_162_1302)::[])
in (_162_1304)::_162_1303))
in (_162_1306)::_162_1305))
in (typing_pred_y)::_162_1307)
in (typing_pred)::_162_1308)
in (FStar_SMTEncoding_Term.mk_and_l _162_1309))
in (_162_1310, precedes_y_x))
in (FStar_SMTEncoding_Term.mkImp _162_1311))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _162_1312))
in (mkForall_fuel _162_1313))
in (_162_1314, Some ("well-founded ordering on nat (alt)")))
in FStar_SMTEncoding_Term.Assume (_162_1315))
in (_162_1316)::[])
in (_162_1318)::_162_1317))
in (_162_1320)::_162_1319)))))))))))
in (
# 1083 "FStar.SMTEncoding.Encode.fst"
let mk_int_alias = (fun env nm tt -> (let _162_1331 = (let _162_1330 = (let _162_1329 = (let _162_1328 = (let _162_1327 = (FStar_SMTEncoding_Term.mkApp (FStar_Syntax_Const.int_lid.FStar_Ident.str, []))
in (tt, _162_1327))
in (FStar_SMTEncoding_Term.mkEq _162_1328))
in (_162_1329, Some ("mapping to int; for now")))
in FStar_SMTEncoding_Term.Assume (_162_1330))
in (_162_1331)::[]))
in (
# 1085 "FStar.SMTEncoding.Encode.fst"
let mk_str = (fun env nm tt -> (
# 1086 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (
# 1087 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.String_sort)
in (
# 1088 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (let _162_1354 = (let _162_1343 = (let _162_1342 = (let _162_1341 = (let _162_1340 = (let _162_1339 = (let _162_1338 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in (typing_pred, _162_1338))
in (FStar_SMTEncoding_Term.mkImp _162_1339))
in (((typing_pred)::[])::[], (xx)::[], _162_1340))
in (mkForall_fuel _162_1341))
in (_162_1342, Some ("string inversion")))
in FStar_SMTEncoding_Term.Assume (_162_1343))
in (let _162_1353 = (let _162_1352 = (let _162_1351 = (let _162_1350 = (let _162_1349 = (let _162_1348 = (let _162_1345 = (let _162_1344 = (FStar_SMTEncoding_Term.boxString b)
in (_162_1344)::[])
in (_162_1345)::[])
in (let _162_1347 = (let _162_1346 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType _162_1346 tt))
in (_162_1348, (bb)::[], _162_1347)))
in (FStar_SMTEncoding_Term.mkForall _162_1349))
in (_162_1350, Some ("string typing")))
in FStar_SMTEncoding_Term.Assume (_162_1351))
in (_162_1352)::[])
in (_162_1354)::_162_1353))))))
in (
# 1091 "FStar.SMTEncoding.Encode.fst"
let mk_ref = (fun env reft_name _78_1778 -> (
# 1092 "FStar.SMTEncoding.Encode.fst"
let r = ("r", FStar_SMTEncoding_Term.Ref_sort)
in (
# 1093 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1094 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1095 "FStar.SMTEncoding.Encode.fst"
let refa = (let _162_1363 = (let _162_1362 = (let _162_1361 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (_162_1361)::[])
in (reft_name, _162_1362))
in (FStar_SMTEncoding_Term.mkApp _162_1363))
in (
# 1096 "FStar.SMTEncoding.Encode.fst"
let refb = (let _162_1366 = (let _162_1365 = (let _162_1364 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_162_1364)::[])
in (reft_name, _162_1365))
in (FStar_SMTEncoding_Term.mkApp _162_1366))
in (
# 1097 "FStar.SMTEncoding.Encode.fst"
let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (
# 1098 "FStar.SMTEncoding.Encode.fst"
let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (let _162_1385 = (let _162_1372 = (let _162_1371 = (let _162_1370 = (let _162_1369 = (let _162_1368 = (let _162_1367 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in (typing_pred, _162_1367))
in (FStar_SMTEncoding_Term.mkImp _162_1368))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _162_1369))
in (mkForall_fuel _162_1370))
in (_162_1371, Some ("ref inversion")))
in FStar_SMTEncoding_Term.Assume (_162_1372))
in (let _162_1384 = (let _162_1383 = (let _162_1382 = (let _162_1381 = (let _162_1380 = (let _162_1379 = (let _162_1378 = (let _162_1377 = (FStar_SMTEncoding_Term.mkAnd (typing_pred, typing_pred_b))
in (let _162_1376 = (let _162_1375 = (let _162_1374 = (FStar_SMTEncoding_Term.mkFreeV aa)
in (let _162_1373 = (FStar_SMTEncoding_Term.mkFreeV bb)
in (_162_1374, _162_1373)))
in (FStar_SMTEncoding_Term.mkEq _162_1375))
in (_162_1377, _162_1376)))
in (FStar_SMTEncoding_Term.mkImp _162_1378))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _162_1379))
in (mkForall_fuel' 2 _162_1380))
in (_162_1381, Some ("ref typing is injective")))
in FStar_SMTEncoding_Term.Assume (_162_1382))
in (_162_1383)::[])
in (_162_1385)::_162_1384))))))))))
in (
# 1101 "FStar.SMTEncoding.Encode.fst"
let mk_false_interp = (fun env nm false_tm -> (
# 1102 "FStar.SMTEncoding.Encode.fst"
let valid = (FStar_SMTEncoding_Term.mkApp ("Valid", (false_tm)::[]))
in (let _162_1394 = (let _162_1393 = (let _162_1392 = (FStar_SMTEncoding_Term.mkIff (FStar_SMTEncoding_Term.mkFalse, valid))
in (_162_1392, Some ("False interpretation")))
in FStar_SMTEncoding_Term.Assume (_162_1393))
in (_162_1394)::[])))
in (
# 1104 "FStar.SMTEncoding.Encode.fst"
let mk_and_interp = (fun env conj _78_1795 -> (
# 1105 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1106 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1107 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1108 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1109 "FStar.SMTEncoding.Encode.fst"
let valid = (let _162_1403 = (let _162_1402 = (let _162_1401 = (FStar_SMTEncoding_Term.mkApp (conj, (a)::(b)::[]))
in (_162_1401)::[])
in ("Valid", _162_1402))
in (FStar_SMTEncoding_Term.mkApp _162_1403))
in (
# 1110 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1111 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _162_1410 = (let _162_1409 = (let _162_1408 = (let _162_1407 = (let _162_1406 = (let _162_1405 = (let _162_1404 = (FStar_SMTEncoding_Term.mkAnd (valid_a, valid_b))
in (_162_1404, valid))
in (FStar_SMTEncoding_Term.mkIff _162_1405))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1406))
in (FStar_SMTEncoding_Term.mkForall _162_1407))
in (_162_1408, Some ("/\\ interpretation")))
in FStar_SMTEncoding_Term.Assume (_162_1409))
in (_162_1410)::[])))))))))
in (
# 1113 "FStar.SMTEncoding.Encode.fst"
let mk_or_interp = (fun env disj _78_1807 -> (
# 1114 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1115 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1116 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1117 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1118 "FStar.SMTEncoding.Encode.fst"
let valid = (let _162_1419 = (let _162_1418 = (let _162_1417 = (FStar_SMTEncoding_Term.mkApp (disj, (a)::(b)::[]))
in (_162_1417)::[])
in ("Valid", _162_1418))
in (FStar_SMTEncoding_Term.mkApp _162_1419))
in (
# 1119 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1120 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _162_1426 = (let _162_1425 = (let _162_1424 = (let _162_1423 = (let _162_1422 = (let _162_1421 = (let _162_1420 = (FStar_SMTEncoding_Term.mkOr (valid_a, valid_b))
in (_162_1420, valid))
in (FStar_SMTEncoding_Term.mkIff _162_1421))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1422))
in (FStar_SMTEncoding_Term.mkForall _162_1423))
in (_162_1424, Some ("\\/ interpretation")))
in FStar_SMTEncoding_Term.Assume (_162_1425))
in (_162_1426)::[])))))))))
in (
# 1122 "FStar.SMTEncoding.Encode.fst"
let mk_eq2_interp = (fun env eq2 tt -> (
# 1123 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1124 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1125 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1126 "FStar.SMTEncoding.Encode.fst"
let yy = ("y", FStar_SMTEncoding_Term.Term_sort)
in (
# 1127 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1128 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1129 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1130 "FStar.SMTEncoding.Encode.fst"
let y = (FStar_SMTEncoding_Term.mkFreeV yy)
in (
# 1131 "FStar.SMTEncoding.Encode.fst"
let valid = (let _162_1435 = (let _162_1434 = (let _162_1433 = (FStar_SMTEncoding_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_162_1433)::[])
in ("Valid", _162_1434))
in (FStar_SMTEncoding_Term.mkApp _162_1435))
in (let _162_1442 = (let _162_1441 = (let _162_1440 = (let _162_1439 = (let _162_1438 = (let _162_1437 = (let _162_1436 = (FStar_SMTEncoding_Term.mkEq (x, y))
in (_162_1436, valid))
in (FStar_SMTEncoding_Term.mkIff _162_1437))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _162_1438))
in (FStar_SMTEncoding_Term.mkForall _162_1439))
in (_162_1440, Some ("Eq2 interpretation")))
in FStar_SMTEncoding_Term.Assume (_162_1441))
in (_162_1442)::[])))))))))))
in (
# 1133 "FStar.SMTEncoding.Encode.fst"
let mk_imp_interp = (fun env imp tt -> (
# 1134 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1135 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1136 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1137 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1138 "FStar.SMTEncoding.Encode.fst"
let valid = (let _162_1451 = (let _162_1450 = (let _162_1449 = (FStar_SMTEncoding_Term.mkApp (imp, (a)::(b)::[]))
in (_162_1449)::[])
in ("Valid", _162_1450))
in (FStar_SMTEncoding_Term.mkApp _162_1451))
in (
# 1139 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1140 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _162_1458 = (let _162_1457 = (let _162_1456 = (let _162_1455 = (let _162_1454 = (let _162_1453 = (let _162_1452 = (FStar_SMTEncoding_Term.mkImp (valid_a, valid_b))
in (_162_1452, valid))
in (FStar_SMTEncoding_Term.mkIff _162_1453))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1454))
in (FStar_SMTEncoding_Term.mkForall _162_1455))
in (_162_1456, Some ("==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_162_1457))
in (_162_1458)::[])))))))))
in (
# 1142 "FStar.SMTEncoding.Encode.fst"
let mk_iff_interp = (fun env iff tt -> (
# 1143 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1144 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1145 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1146 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1147 "FStar.SMTEncoding.Encode.fst"
let valid = (let _162_1467 = (let _162_1466 = (let _162_1465 = (FStar_SMTEncoding_Term.mkApp (iff, (a)::(b)::[]))
in (_162_1465)::[])
in ("Valid", _162_1466))
in (FStar_SMTEncoding_Term.mkApp _162_1467))
in (
# 1148 "FStar.SMTEncoding.Encode.fst"
let valid_a = (FStar_SMTEncoding_Term.mkApp ("Valid", (a)::[]))
in (
# 1149 "FStar.SMTEncoding.Encode.fst"
let valid_b = (FStar_SMTEncoding_Term.mkApp ("Valid", (b)::[]))
in (let _162_1474 = (let _162_1473 = (let _162_1472 = (let _162_1471 = (let _162_1470 = (let _162_1469 = (let _162_1468 = (FStar_SMTEncoding_Term.mkIff (valid_a, valid_b))
in (_162_1468, valid))
in (FStar_SMTEncoding_Term.mkIff _162_1469))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1470))
in (FStar_SMTEncoding_Term.mkForall _162_1471))
in (_162_1472, Some ("<==> interpretation")))
in FStar_SMTEncoding_Term.Assume (_162_1473))
in (_162_1474)::[])))))))))
in (
# 1151 "FStar.SMTEncoding.Encode.fst"
let mk_forall_interp = (fun env for_all tt -> (
# 1152 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1153 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1154 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1155 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1156 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1157 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1158 "FStar.SMTEncoding.Encode.fst"
let valid = (let _162_1483 = (let _162_1482 = (let _162_1481 = (FStar_SMTEncoding_Term.mkApp (for_all, (a)::(b)::[]))
in (_162_1481)::[])
in ("Valid", _162_1482))
in (FStar_SMTEncoding_Term.mkApp _162_1483))
in (
# 1159 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _162_1486 = (let _162_1485 = (let _162_1484 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_162_1484)::[])
in ("Valid", _162_1485))
in (FStar_SMTEncoding_Term.mkApp _162_1486))
in (let _162_1500 = (let _162_1499 = (let _162_1498 = (let _162_1497 = (let _162_1496 = (let _162_1495 = (let _162_1494 = (let _162_1493 = (let _162_1492 = (let _162_1488 = (let _162_1487 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_162_1487)::[])
in (_162_1488)::[])
in (let _162_1491 = (let _162_1490 = (let _162_1489 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_162_1489, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _162_1490))
in (_162_1492, (xx)::[], _162_1491)))
in (FStar_SMTEncoding_Term.mkForall _162_1493))
in (_162_1494, valid))
in (FStar_SMTEncoding_Term.mkIff _162_1495))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1496))
in (FStar_SMTEncoding_Term.mkForall _162_1497))
in (_162_1498, Some ("forall interpretation")))
in FStar_SMTEncoding_Term.Assume (_162_1499))
in (_162_1500)::[]))))))))))
in (
# 1161 "FStar.SMTEncoding.Encode.fst"
let mk_exists_interp = (fun env for_some tt -> (
# 1162 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1163 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1164 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1165 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1166 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1167 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1168 "FStar.SMTEncoding.Encode.fst"
let valid = (let _162_1509 = (let _162_1508 = (let _162_1507 = (FStar_SMTEncoding_Term.mkApp (for_some, (a)::(b)::[]))
in (_162_1507)::[])
in ("Valid", _162_1508))
in (FStar_SMTEncoding_Term.mkApp _162_1509))
in (
# 1169 "FStar.SMTEncoding.Encode.fst"
let valid_b_x = (let _162_1512 = (let _162_1511 = (let _162_1510 = (FStar_SMTEncoding_Term.mk_ApplyTT b x)
in (_162_1510)::[])
in ("Valid", _162_1511))
in (FStar_SMTEncoding_Term.mkApp _162_1512))
in (let _162_1526 = (let _162_1525 = (let _162_1524 = (let _162_1523 = (let _162_1522 = (let _162_1521 = (let _162_1520 = (let _162_1519 = (let _162_1518 = (let _162_1514 = (let _162_1513 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_162_1513)::[])
in (_162_1514)::[])
in (let _162_1517 = (let _162_1516 = (let _162_1515 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (_162_1515, valid_b_x))
in (FStar_SMTEncoding_Term.mkImp _162_1516))
in (_162_1518, (xx)::[], _162_1517)))
in (FStar_SMTEncoding_Term.mkExists _162_1519))
in (_162_1520, valid))
in (FStar_SMTEncoding_Term.mkIff _162_1521))
in (((valid)::[])::[], (aa)::(bb)::[], _162_1522))
in (FStar_SMTEncoding_Term.mkForall _162_1523))
in (_162_1524, Some ("exists interpretation")))
in FStar_SMTEncoding_Term.Assume (_162_1525))
in (_162_1526)::[]))))))))))
in (
# 1171 "FStar.SMTEncoding.Encode.fst"
let mk_range_of_interp = (fun env range_of tt -> (
# 1172 "FStar.SMTEncoding.Encode.fst"
let aa = ("a", FStar_SMTEncoding_Term.Term_sort)
in (
# 1173 "FStar.SMTEncoding.Encode.fst"
let bb = ("b", FStar_SMTEncoding_Term.Term_sort)
in (
# 1174 "FStar.SMTEncoding.Encode.fst"
let a = (FStar_SMTEncoding_Term.mkFreeV aa)
in (
# 1175 "FStar.SMTEncoding.Encode.fst"
let b = (FStar_SMTEncoding_Term.mkFreeV bb)
in (
# 1176 "FStar.SMTEncoding.Encode.fst"
let range_of_ty = (FStar_SMTEncoding_Term.mkApp (range_of, (a)::(b)::[]))
in (let _162_1537 = (let _162_1536 = (let _162_1535 = (let _162_1534 = (let _162_1533 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_of_ty)
in (((range_of_ty)::[])::[], (aa)::(bb)::[], _162_1533))
in (FStar_SMTEncoding_Term.mkForall _162_1534))
in (_162_1535, Some ("Range_const typing")))
in FStar_SMTEncoding_Term.Assume (_162_1536))
in (_162_1537)::[])))))))
in (
# 1183 "FStar.SMTEncoding.Encode.fst"
let prims = ((FStar_Syntax_Const.unit_lid, mk_unit))::((FStar_Syntax_Const.bool_lid, mk_bool))::((FStar_Syntax_Const.int_lid, mk_int))::((FStar_Syntax_Const.string_lid, mk_str))::((FStar_Syntax_Const.ref_lid, mk_ref))::((FStar_Syntax_Const.char_lid, mk_int_alias))::((FStar_Syntax_Const.uint8_lid, mk_int_alias))::((FStar_Syntax_Const.false_lid, mk_false_interp))::((FStar_Syntax_Const.and_lid, mk_and_interp))::((FStar_Syntax_Const.or_lid, mk_or_interp))::((FStar_Syntax_Const.eq2_lid, mk_eq2_interp))::((FStar_Syntax_Const.imp_lid, mk_imp_interp))::((FStar_Syntax_Const.iff_lid, mk_iff_interp))::((FStar_Syntax_Const.forall_lid, mk_forall_interp))::((FStar_Syntax_Const.exists_lid, mk_exists_interp))::((FStar_Syntax_Const.range_of_lid, mk_range_of_interp))::[]
in (fun env t s tt -> (match ((FStar_Util.find_opt (fun _78_1893 -> (match (_78_1893) with
| (l, _78_1892) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_78_1896, f) -> begin
(f env s tt)
end))))))))))))))))))))))

# 1206 "FStar.SMTEncoding.Encode.fst"
let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1207 "FStar.SMTEncoding.Encode.fst"
let _78_1902 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding"))) then begin
(let _162_1749 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _162_1749))
end else begin
()
end
in (
# 1210 "FStar.SMTEncoding.Encode.fst"
let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (
# 1213 "FStar.SMTEncoding.Encode.fst"
let _78_1910 = (encode_sigelt' env se)
in (match (_78_1910) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _162_1752 = (let _162_1751 = (let _162_1750 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (_162_1750))
in (_162_1751)::[])
in (_162_1752, e))
end
| _78_1913 -> begin
(let _162_1759 = (let _162_1758 = (let _162_1754 = (let _162_1753 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_162_1753))
in (_162_1754)::g)
in (let _162_1757 = (let _162_1756 = (let _162_1755 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (_162_1755))
in (_162_1756)::[])
in (FStar_List.append _162_1758 _162_1757)))
in (_162_1759, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (
# 1219 "FStar.SMTEncoding.Encode.fst"
let should_skip = (fun l -> false)
in (
# 1225 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_val = (fun env lid t quals -> (
# 1226 "FStar.SMTEncoding.Encode.fst"
let tt = (norm env t)
in (
# 1232 "FStar.SMTEncoding.Encode.fst"
let _78_1926 = (encode_free_var env lid t tt quals)
in (match (_78_1926) with
| (decls, env) -> begin
if (FStar_Syntax_Util.is_smt_lemma t) then begin
(let _162_1773 = (let _162_1772 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls _162_1772))
in (_162_1773, env))
end else begin
(decls, env)
end
end))))
in (
# 1238 "FStar.SMTEncoding.Encode.fst"
let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _78_1933 lb -> (match (_78_1933) with
| (decls, env) -> begin
(
# 1240 "FStar.SMTEncoding.Encode.fst"
let _78_1937 = (let _162_1782 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env _162_1782 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (_78_1937) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_new_effect (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _78_1955, _78_1957, _78_1959, _78_1961) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(
# 1252 "FStar.SMTEncoding.Encode.fst"
let _78_1967 = (new_term_constant_and_tok_from_lid env lid)
in (match (_78_1967) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, _78_1970, t, quals, _78_1974) -> begin
(
# 1256 "FStar.SMTEncoding.Encode.fst"
let will_encode_definition = (not ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_12 -> (match (_78_12) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| _78_1987 -> begin
false
end))))))
in if will_encode_definition then begin
([], env)
end else begin
(
# 1261 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (
# 1262 "FStar.SMTEncoding.Encode.fst"
let _78_1992 = (encode_top_level_val env fv t quals)
in (match (_78_1992) with
| (decls, env) -> begin
(
# 1263 "FStar.SMTEncoding.Encode.fst"
let tname = lid.FStar_Ident.str
in (
# 1264 "FStar.SMTEncoding.Encode.fst"
let tsym = (FStar_SMTEncoding_Term.mkFreeV (tname, FStar_SMTEncoding_Term.Term_sort))
in (let _162_1785 = (let _162_1784 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls _162_1784))
in (_162_1785, env))))
end)))
end)
end
| FStar_Syntax_Syntax.Sig_assume (l, f, _78_1998, _78_2000) -> begin
(
# 1270 "FStar.SMTEncoding.Encode.fst"
let _78_2005 = (encode_formula f env)
in (match (_78_2005) with
| (f, decls) -> begin
(
# 1271 "FStar.SMTEncoding.Encode.fst"
let g = (let _162_1790 = (let _162_1789 = (let _162_1788 = (let _162_1787 = (let _162_1786 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" _162_1786))
in Some (_162_1787))
in (f, _162_1788))
in FStar_SMTEncoding_Term.Assume (_162_1789))
in (_162_1790)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, _78_2010, quals) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((_78_2015, {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = _78_2023; FStar_Syntax_Syntax.lbtyp = _78_2021; FStar_Syntax_Syntax.lbeff = _78_2019; FStar_Syntax_Syntax.lbdef = _78_2017}::[]), _78_2030, _78_2032, _78_2034) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(
# 1278 "FStar.SMTEncoding.Encode.fst"
let _78_2040 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_78_2040) with
| (tname, ttok, env) -> begin
(
# 1279 "FStar.SMTEncoding.Encode.fst"
let xx = ("x", FStar_SMTEncoding_Term.Term_sort)
in (
# 1280 "FStar.SMTEncoding.Encode.fst"
let x = (FStar_SMTEncoding_Term.mkFreeV xx)
in (
# 1281 "FStar.SMTEncoding.Encode.fst"
let valid_b2t_x = (let _162_1793 = (let _162_1792 = (let _162_1791 = (FStar_SMTEncoding_Term.mkApp ("Prims.b2t", (x)::[]))
in (_162_1791)::[])
in ("Valid", _162_1792))
in (FStar_SMTEncoding_Term.mkApp _162_1793))
in (
# 1282 "FStar.SMTEncoding.Encode.fst"
let decls = (let _162_1801 = (let _162_1800 = (let _162_1799 = (let _162_1798 = (let _162_1797 = (let _162_1796 = (let _162_1795 = (let _162_1794 = (FStar_SMTEncoding_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _162_1794))
in (FStar_SMTEncoding_Term.mkEq _162_1795))
in (((valid_b2t_x)::[])::[], (xx)::[], _162_1796))
in (FStar_SMTEncoding_Term.mkForall _162_1797))
in (_162_1798, Some ("b2t def")))
in FStar_SMTEncoding_Term.Assume (_162_1799))
in (_162_1800)::[])
in (FStar_SMTEncoding_Term.DeclFun ((tname, (FStar_SMTEncoding_Term.Term_sort)::[], FStar_SMTEncoding_Term.Term_sort, None)))::_162_1801)
in (decls, env)))))
end))
end
| FStar_Syntax_Syntax.Sig_let (_78_2046, _78_2048, _78_2050, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_13 -> (match (_78_13) with
| (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Inline) -> begin
true
end
| _78_2060 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_let ((false, lb::[]), _78_2066, _78_2068, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_14 -> (match (_78_14) with
| FStar_Syntax_Syntax.Projector (_78_2074) -> begin
true
end
| _78_2077 -> begin
false
end)))) -> begin
(
# 1296 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 1297 "FStar.SMTEncoding.Encode.fst"
let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (match ((try_lookup_free_var env l)) with
| Some (_78_2081) -> begin
([], env)
end
| None -> begin
(
# 1302 "FStar.SMTEncoding.Encode.fst"
let se = FStar_Syntax_Syntax.Sig_declare_typ ((l, lb.FStar_Syntax_Syntax.lbunivs, lb.FStar_Syntax_Syntax.lbtyp, quals, (FStar_Ident.range_of_lid l)))
in (encode_sigelt env se))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), _78_2089, _78_2091, quals) -> begin
(
# 1308 "FStar.SMTEncoding.Encode.fst"
let eta_expand = (fun binders formals body t -> (
# 1309 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1310 "FStar.SMTEncoding.Encode.fst"
let _78_2103 = (FStar_Util.first_N nbinders formals)
in (match (_78_2103) with
| (formals, extra_formals) -> begin
(
# 1311 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _78_2107 _78_2111 -> (match ((_78_2107, _78_2111)) with
| ((formal, _78_2106), (binder, _78_2110)) -> begin
(let _162_1815 = (let _162_1814 = (FStar_Syntax_Syntax.bv_to_name binder)
in (formal, _162_1814))
in FStar_Syntax_Syntax.NT (_162_1815))
end)) formals binders)
in (
# 1312 "FStar.SMTEncoding.Encode.fst"
let extra_formals = (let _162_1819 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun _78_2115 -> (match (_78_2115) with
| (x, i) -> begin
(let _162_1818 = (
# 1312 "FStar.SMTEncoding.Encode.fst"
let _78_2116 = x
in (let _162_1817 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _78_2116.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _78_2116.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _162_1817}))
in (_162_1818, i))
end))))
in (FStar_All.pipe_right _162_1819 FStar_Syntax_Util.name_binders))
in (
# 1313 "FStar.SMTEncoding.Encode.fst"
let body = (let _162_1826 = (FStar_Syntax_Subst.compress body)
in (let _162_1825 = (let _162_1820 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _162_1820))
in (let _162_1824 = (let _162_1823 = (let _162_1822 = (FStar_Syntax_Subst.subst subst t)
in _162_1822.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _162_1821 -> Some (_162_1821)) _162_1823))
in (FStar_Syntax_Syntax.extend_app_n _162_1826 _162_1825 _162_1824 body.FStar_Syntax_Syntax.pos))))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (
# 1316 "FStar.SMTEncoding.Encode.fst"
let rec destruct_bound_function = (fun flid t_norm e -> (match ((let _162_1833 = (FStar_Syntax_Util.unascribe e)
in _162_1833.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(
# 1319 "FStar.SMTEncoding.Encode.fst"
let _78_2132 = (FStar_Syntax_Subst.open_term' binders body)
in (match (_78_2132) with
| (binders, body, opening) -> begin
(match ((let _162_1834 = (FStar_Syntax_Subst.compress t_norm)
in _162_1834.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1322 "FStar.SMTEncoding.Encode.fst"
let _78_2139 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_78_2139) with
| (formals, c) -> begin
(
# 1323 "FStar.SMTEncoding.Encode.fst"
let nformals = (FStar_List.length formals)
in (
# 1324 "FStar.SMTEncoding.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1325 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c)) then begin
(
# 1327 "FStar.SMTEncoding.Encode.fst"
let lopt = (subst_lcomp_opt opening lopt)
in (
# 1328 "FStar.SMTEncoding.Encode.fst"
let _78_2146 = (FStar_Util.first_N nformals binders)
in (match (_78_2146) with
| (bs0, rest) -> begin
(
# 1329 "FStar.SMTEncoding.Encode.fst"
let c = (
# 1330 "FStar.SMTEncoding.Encode.fst"
let subst = (FStar_List.map2 (fun _78_2150 _78_2154 -> (match ((_78_2150, _78_2154)) with
| ((b, _78_2149), (x, _78_2153)) -> begin
(let _162_1838 = (let _162_1837 = (FStar_Syntax_Syntax.bv_to_name x)
in (b, _162_1837))
in FStar_Syntax_Syntax.NT (_162_1838))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (
# 1332 "FStar.SMTEncoding.Encode.fst"
let body = (FStar_Syntax_Util.abs rest body lopt)
in (bs0, body, bs0, (FStar_Syntax_Util.comp_result c))))
end)))
end else begin
if (nformals > nbinders) then begin
(
# 1335 "FStar.SMTEncoding.Encode.fst"
let _78_2160 = (eta_expand binders formals body tres)
in (match (_78_2160) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end))
end
| _78_2162 -> begin
(let _162_1841 = (let _162_1840 = (FStar_Syntax_Print.term_to_string e)
in (let _162_1839 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _162_1840 _162_1839)))
in (FStar_All.failwith _162_1841))
end)
end))
end
| _78_2164 -> begin
(match ((let _162_1842 = (FStar_Syntax_Subst.compress t_norm)
in _162_1842.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(
# 1345 "FStar.SMTEncoding.Encode.fst"
let _78_2171 = (FStar_Syntax_Subst.open_comp formals c)
in (match (_78_2171) with
| (formals, c) -> begin
(
# 1346 "FStar.SMTEncoding.Encode.fst"
let tres = (FStar_Syntax_Util.comp_result c)
in (
# 1347 "FStar.SMTEncoding.Encode.fst"
let _78_2175 = (eta_expand [] formals e tres)
in (match (_78_2175) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end))
end
| _78_2177 -> begin
([], e, [], t_norm)
end)
end))
in (FStar_All.try_with (fun _78_2179 -> (match (()) with
| () -> begin
if (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(
# 1355 "FStar.SMTEncoding.Encode.fst"
let _78_2205 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _78_2192 lb -> (match (_78_2192) with
| (toks, typs, decls, env) -> begin
(
# 1357 "FStar.SMTEncoding.Encode.fst"
let _78_2194 = if (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (
# 1358 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (
# 1359 "FStar.SMTEncoding.Encode.fst"
let _78_2200 = (let _162_1847 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env _162_1847 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (_78_2200) with
| (tok, decl, env) -> begin
(let _162_1850 = (let _162_1849 = (let _162_1848 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (_162_1848, tok))
in (_162_1849)::toks)
in (_162_1850, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_78_2205) with
| (toks, typs, decls, env) -> begin
(
# 1361 "FStar.SMTEncoding.Encode.fst"
let toks = (FStar_List.rev toks)
in (
# 1362 "FStar.SMTEncoding.Encode.fst"
let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (
# 1363 "FStar.SMTEncoding.Encode.fst"
let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_15 -> (match (_78_15) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| _78_2212 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (let _162_1853 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _162_1853)))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Syntax_Syntax.lbname = _78_2222; FStar_Syntax_Syntax.lbunivs = _78_2220; FStar_Syntax_Syntax.lbtyp = _78_2218; FStar_Syntax_Syntax.lbeff = _78_2216; FStar_Syntax_Syntax.lbdef = e}::[], t_norm::[], (flid_fv, (f, ftok))::[]) -> begin
(
# 1370 "FStar.SMTEncoding.Encode.fst"
let e = (FStar_Syntax_Subst.compress e)
in (
# 1371 "FStar.SMTEncoding.Encode.fst"
let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1372 "FStar.SMTEncoding.Encode.fst"
let _78_2242 = (destruct_bound_function flid t_norm e)
in (match (_78_2242) with
| (binders, body, _78_2239, _78_2241) -> begin
(
# 1373 "FStar.SMTEncoding.Encode.fst"
let _78_2249 = (encode_binders None binders env)
in (match (_78_2249) with
| (vars, guards, env', binder_decls, _78_2248) -> begin
(
# 1374 "FStar.SMTEncoding.Encode.fst"
let app = (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (f, FStar_SMTEncoding_Term.Term_sort))
end
| _78_2252 -> begin
(let _162_1855 = (let _162_1854 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (f, _162_1854))
in (FStar_SMTEncoding_Term.mkApp _162_1855))
end)
in (
# 1375 "FStar.SMTEncoding.Encode.fst"
let _78_2258 = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic)) then begin
(let _162_1857 = (FStar_SMTEncoding_Term.mk_Valid app)
in (let _162_1856 = (encode_formula body env')
in (_162_1857, _162_1856)))
end else begin
(let _162_1858 = (encode_term body env')
in (app, _162_1858))
end
in (match (_78_2258) with
| (app, (body, decls2)) -> begin
(
# 1379 "FStar.SMTEncoding.Encode.fst"
let eqn = (let _162_1867 = (let _162_1866 = (let _162_1863 = (let _162_1862 = (let _162_1861 = (let _162_1860 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _162_1859 = (FStar_SMTEncoding_Term.mkEq (app, body))
in (_162_1860, _162_1859)))
in (FStar_SMTEncoding_Term.mkImp _162_1861))
in (((app)::[])::[], vars, _162_1862))
in (FStar_SMTEncoding_Term.mkForall _162_1863))
in (let _162_1865 = (let _162_1864 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_162_1864))
in (_162_1866, _162_1865)))
in FStar_SMTEncoding_Term.Assume (_162_1867))
in (let _162_1869 = (let _162_1868 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])) _162_1868))
in (_162_1869, env)))
end)))
end))
end))))
end
| _78_2261 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 1385 "FStar.SMTEncoding.Encode.fst"
let fuel = (let _162_1870 = (varops.fresh "fuel")
in (_162_1870, FStar_SMTEncoding_Term.Fuel_sort))
in (
# 1386 "FStar.SMTEncoding.Encode.fst"
let fuel_tm = (FStar_SMTEncoding_Term.mkFreeV fuel)
in (
# 1387 "FStar.SMTEncoding.Encode.fst"
let env0 = env
in (
# 1388 "FStar.SMTEncoding.Encode.fst"
let _78_2279 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _78_2267 _78_2272 -> (match ((_78_2267, _78_2272)) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(
# 1389 "FStar.SMTEncoding.Encode.fst"
let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1390 "FStar.SMTEncoding.Encode.fst"
let g = (varops.new_fvar flid)
in (
# 1391 "FStar.SMTEncoding.Encode.fst"
let gtok = (varops.new_fvar flid)
in (
# 1392 "FStar.SMTEncoding.Encode.fst"
let env = (let _162_1875 = (let _162_1874 = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _162_1873 -> Some (_162_1873)) _162_1874))
in (push_free_var env flid gtok _162_1875))
in (((flid, f, ftok, g, gtok))::gtoks, env)))))
end)) ([], env)))
in (match (_78_2279) with
| (gtoks, env) -> begin
(
# 1394 "FStar.SMTEncoding.Encode.fst"
let gtoks = (FStar_List.rev gtoks)
in (
# 1395 "FStar.SMTEncoding.Encode.fst"
let encode_one_binding = (fun env0 _78_2288 t_norm _78_2299 -> (match ((_78_2288, _78_2299)) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = _78_2298; FStar_Syntax_Syntax.lbunivs = _78_2296; FStar_Syntax_Syntax.lbtyp = _78_2294; FStar_Syntax_Syntax.lbeff = _78_2292; FStar_Syntax_Syntax.lbdef = e}) -> begin
(
# 1396 "FStar.SMTEncoding.Encode.fst"
let _78_2304 = (destruct_bound_function flid t_norm e)
in (match (_78_2304) with
| (binders, body, formals, tres) -> begin
(
# 1397 "FStar.SMTEncoding.Encode.fst"
let _78_2311 = (encode_binders None binders env)
in (match (_78_2311) with
| (vars, guards, env', binder_decls, _78_2310) -> begin
(
# 1398 "FStar.SMTEncoding.Encode.fst"
let decl_g = (let _162_1886 = (let _162_1885 = (let _162_1884 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::_162_1884)
in (g, _162_1885, FStar_SMTEncoding_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_SMTEncoding_Term.DeclFun (_162_1886))
in (
# 1399 "FStar.SMTEncoding.Encode.fst"
let env0 = (push_zfuel_name env0 flid g)
in (
# 1400 "FStar.SMTEncoding.Encode.fst"
let decl_g_tok = FStar_SMTEncoding_Term.DeclFun ((gtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (
# 1401 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1402 "FStar.SMTEncoding.Encode.fst"
let app = (FStar_SMTEncoding_Term.mkApp (f, vars_tm))
in (
# 1403 "FStar.SMTEncoding.Encode.fst"
let gsapp = (let _162_1889 = (let _162_1888 = (let _162_1887 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_162_1887)::vars_tm)
in (g, _162_1888))
in (FStar_SMTEncoding_Term.mkApp _162_1889))
in (
# 1404 "FStar.SMTEncoding.Encode.fst"
let gmax = (let _162_1892 = (let _162_1891 = (let _162_1890 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (_162_1890)::vars_tm)
in (g, _162_1891))
in (FStar_SMTEncoding_Term.mkApp _162_1892))
in (
# 1405 "FStar.SMTEncoding.Encode.fst"
let _78_2321 = (encode_term body env')
in (match (_78_2321) with
| (body_tm, decls2) -> begin
(
# 1406 "FStar.SMTEncoding.Encode.fst"
let eqn_g = (let _162_1901 = (let _162_1900 = (let _162_1897 = (let _162_1896 = (let _162_1895 = (let _162_1894 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (let _162_1893 = (FStar_SMTEncoding_Term.mkEq (gsapp, body_tm))
in (_162_1894, _162_1893)))
in (FStar_SMTEncoding_Term.mkImp _162_1895))
in (((gsapp)::[])::[], (fuel)::vars, _162_1896))
in (FStar_SMTEncoding_Term.mkForall _162_1897))
in (let _162_1899 = (let _162_1898 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_162_1898))
in (_162_1900, _162_1899)))
in FStar_SMTEncoding_Term.Assume (_162_1901))
in (
# 1408 "FStar.SMTEncoding.Encode.fst"
let eqn_f = (let _162_1905 = (let _162_1904 = (let _162_1903 = (let _162_1902 = (FStar_SMTEncoding_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _162_1902))
in (FStar_SMTEncoding_Term.mkForall _162_1903))
in (_162_1904, Some ("Correspondence of recursive function to instrumented version")))
in FStar_SMTEncoding_Term.Assume (_162_1905))
in (
# 1410 "FStar.SMTEncoding.Encode.fst"
let eqn_g' = (let _162_1914 = (let _162_1913 = (let _162_1912 = (let _162_1911 = (let _162_1910 = (let _162_1909 = (let _162_1908 = (let _162_1907 = (let _162_1906 = (FStar_SMTEncoding_Term.n_fuel 0)
in (_162_1906)::vars_tm)
in (g, _162_1907))
in (FStar_SMTEncoding_Term.mkApp _162_1908))
in (gsapp, _162_1909))
in (FStar_SMTEncoding_Term.mkEq _162_1910))
in (((gsapp)::[])::[], (fuel)::vars, _162_1911))
in (FStar_SMTEncoding_Term.mkForall _162_1912))
in (_162_1913, Some ("Fuel irrelevance")))
in FStar_SMTEncoding_Term.Assume (_162_1914))
in (
# 1412 "FStar.SMTEncoding.Encode.fst"
let _78_2344 = (
# 1413 "FStar.SMTEncoding.Encode.fst"
let _78_2331 = (encode_binders None formals env0)
in (match (_78_2331) with
| (vars, v_guards, env, binder_decls, _78_2330) -> begin
(
# 1414 "FStar.SMTEncoding.Encode.fst"
let vars_tm = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1415 "FStar.SMTEncoding.Encode.fst"
let gapp = (FStar_SMTEncoding_Term.mkApp (g, (fuel_tm)::vars_tm))
in (
# 1416 "FStar.SMTEncoding.Encode.fst"
let tok_corr = (
# 1417 "FStar.SMTEncoding.Encode.fst"
let tok_app = (let _162_1915 = (FStar_SMTEncoding_Term.mkFreeV (gtok, FStar_SMTEncoding_Term.Term_sort))
in (mk_Apply _162_1915 ((fuel)::vars)))
in (let _162_1919 = (let _162_1918 = (let _162_1917 = (let _162_1916 = (FStar_SMTEncoding_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _162_1916))
in (FStar_SMTEncoding_Term.mkForall _162_1917))
in (_162_1918, Some ("Fuel token correspondence")))
in FStar_SMTEncoding_Term.Assume (_162_1919)))
in (
# 1420 "FStar.SMTEncoding.Encode.fst"
let _78_2341 = (
# 1421 "FStar.SMTEncoding.Encode.fst"
let _78_2338 = (encode_term_pred None tres env gapp)
in (match (_78_2338) with
| (g_typing, d3) -> begin
(let _162_1927 = (let _162_1926 = (let _162_1925 = (let _162_1924 = (let _162_1923 = (let _162_1922 = (let _162_1921 = (let _162_1920 = (FStar_SMTEncoding_Term.mk_and_l v_guards)
in (_162_1920, g_typing))
in (FStar_SMTEncoding_Term.mkImp _162_1921))
in (((gapp)::[])::[], (fuel)::vars, _162_1922))
in (FStar_SMTEncoding_Term.mkForall _162_1923))
in (_162_1924, None))
in FStar_SMTEncoding_Term.Assume (_162_1925))
in (_162_1926)::[])
in (d3, _162_1927))
end))
in (match (_78_2341) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_78_2344) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (
# 1425 "FStar.SMTEncoding.Encode.fst"
let _78_2360 = (let _162_1930 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _78_2348 _78_2352 -> (match ((_78_2348, _78_2352)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(
# 1426 "FStar.SMTEncoding.Encode.fst"
let _78_2356 = (encode_one_binding env0 gtok ty bs)
in (match (_78_2356) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _162_1930))
in (match (_78_2360) with
| (decls, eqns, env0) -> begin
(
# 1428 "FStar.SMTEncoding.Encode.fst"
let _78_2369 = (let _162_1932 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _162_1932 (FStar_List.partition (fun _78_16 -> (match (_78_16) with
| FStar_SMTEncoding_Term.DeclFun (_78_2363) -> begin
true
end
| _78_2366 -> begin
false
end)))))
in (match (_78_2369) with
| (prefix_decls, rest) -> begin
(
# 1431 "FStar.SMTEncoding.Encode.fst"
let eqns = (FStar_List.rev eqns)
in ((FStar_List.append (FStar_List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end
end)))
end))
end
end)) (fun _78_2178 -> (match (_78_2178) with
| Let_rec_unencodeable -> begin
(
# 1434 "FStar.SMTEncoding.Encode.fst"
let msg = (let _162_1935 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right _162_1935 (FStar_String.concat " and ")))
in (
# 1435 "FStar.SMTEncoding.Encode.fst"
let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| FStar_Syntax_Syntax.Sig_bundle (ses, _78_2373, _78_2375, _78_2377) -> begin
(
# 1440 "FStar.SMTEncoding.Encode.fst"
let _78_2382 = (encode_signature env ses)
in (match (_78_2382) with
| (g, env) -> begin
(
# 1441 "FStar.SMTEncoding.Encode.fst"
let _78_2394 = (FStar_All.pipe_right g (FStar_List.partition (fun _78_17 -> (match (_78_17) with
| FStar_SMTEncoding_Term.Assume (_78_2385, Some ("inversion axiom")) -> begin
false
end
| _78_2391 -> begin
true
end))))
in (match (_78_2394) with
| (g', inversions) -> begin
(
# 1444 "FStar.SMTEncoding.Encode.fst"
let _78_2403 = (FStar_All.pipe_right g' (FStar_List.partition (fun _78_18 -> (match (_78_18) with
| FStar_SMTEncoding_Term.DeclFun (_78_2397) -> begin
true
end
| _78_2400 -> begin
false
end))))
in (match (_78_2403) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, _78_2406, tps, k, _78_2410, datas, quals, _78_2414) -> begin
(
# 1450 "FStar.SMTEncoding.Encode.fst"
let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _78_19 -> (match (_78_19) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| _78_2421 -> begin
false
end))))
in (
# 1451 "FStar.SMTEncoding.Encode.fst"
let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(
# 1453 "FStar.SMTEncoding.Encode.fst"
let _78_2433 = c
in (match (_78_2433) with
| (name, args, _78_2428, _78_2430, _78_2432) -> begin
(let _162_1943 = (let _162_1942 = (let _162_1941 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _162_1941, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_162_1942))
in (_162_1943)::[])
end))
end else begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end)
in (
# 1457 "FStar.SMTEncoding.Encode.fst"
let inversion_axioms = (fun tapp vars -> if (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _162_1949 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right _162_1949 FStar_Option.isNone))))) then begin
[]
end else begin
(
# 1461 "FStar.SMTEncoding.Encode.fst"
let _78_2440 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (_78_2440) with
| (xxsym, xx) -> begin
(
# 1462 "FStar.SMTEncoding.Encode.fst"
let _78_2476 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _78_2443 l -> (match (_78_2443) with
| (out, decls) -> begin
(
# 1463 "FStar.SMTEncoding.Encode.fst"
let _78_2448 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (_78_2448) with
| (_78_2446, data_t) -> begin
(
# 1464 "FStar.SMTEncoding.Encode.fst"
let _78_2451 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (_78_2451) with
| (args, res) -> begin
(
# 1465 "FStar.SMTEncoding.Encode.fst"
let indices = (match ((let _162_1952 = (FStar_Syntax_Subst.compress res)
in _162_1952.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_app (_78_2453, indices) -> begin
indices
end
| _78_2458 -> begin
[]
end)
in (
# 1468 "FStar.SMTEncoding.Encode.fst"
let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env _78_2464 -> (match (_78_2464) with
| (x, _78_2463) -> begin
(let _162_1957 = (let _162_1956 = (let _162_1955 = (mk_term_projector_name l x)
in (_162_1955, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _162_1956))
in (push_term_var env x _162_1957))
end)) env))
in (
# 1471 "FStar.SMTEncoding.Encode.fst"
let _78_2468 = (encode_args indices env)
in (match (_78_2468) with
| (indices, decls') -> begin
(
# 1472 "FStar.SMTEncoding.Encode.fst"
let _78_2469 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (
# 1474 "FStar.SMTEncoding.Encode.fst"
let eqs = (let _162_1962 = (FStar_List.map2 (fun v a -> (let _162_1961 = (let _162_1960 = (FStar_SMTEncoding_Term.mkFreeV v)
in (_162_1960, a))
in (FStar_SMTEncoding_Term.mkEq _162_1961))) vars indices)
in (FStar_All.pipe_right _162_1962 FStar_SMTEncoding_Term.mk_and_l))
in (let _162_1967 = (let _162_1966 = (let _162_1965 = (let _162_1964 = (let _162_1963 = (mk_data_tester env l xx)
in (_162_1963, eqs))
in (FStar_SMTEncoding_Term.mkAnd _162_1964))
in (out, _162_1965))
in (FStar_SMTEncoding_Term.mkOr _162_1966))
in (_162_1967, (FStar_List.append decls decls')))))
end))))
end))
end))
end)) (FStar_SMTEncoding_Term.mkFalse, [])))
in (match (_78_2476) with
| (data_ax, decls) -> begin
(
# 1476 "FStar.SMTEncoding.Encode.fst"
let _78_2479 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_78_2479) with
| (ffsym, ff) -> begin
(
# 1477 "FStar.SMTEncoding.Encode.fst"
let xx_has_type = (let _162_1968 = (FStar_SMTEncoding_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel _162_1968 xx tapp))
in (let _162_1975 = (let _162_1974 = (let _162_1973 = (let _162_1972 = (let _162_1971 = (let _162_1970 = (add_fuel (ffsym, FStar_SMTEncoding_Term.Fuel_sort) (((xxsym, FStar_SMTEncoding_Term.Term_sort))::vars))
in (let _162_1969 = (FStar_SMTEncoding_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _162_1970, _162_1969)))
in (FStar_SMTEncoding_Term.mkForall _162_1971))
in (_162_1972, Some ("inversion axiom")))
in FStar_SMTEncoding_Term.Assume (_162_1973))
in (_162_1974)::[])
in (FStar_List.append decls _162_1975)))
end))
end))
end))
end)
in (
# 1481 "FStar.SMTEncoding.Encode.fst"
let _78_2489 = (match ((let _162_1976 = (FStar_Syntax_Subst.compress k)
in _162_1976.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
((FStar_List.append tps formals), (FStar_Syntax_Util.comp_result kres))
end
| _78_2486 -> begin
(tps, k)
end)
in (match (_78_2489) with
| (formals, res) -> begin
(
# 1487 "FStar.SMTEncoding.Encode.fst"
let _78_2492 = (FStar_Syntax_Subst.open_term formals res)
in (match (_78_2492) with
| (formals, res) -> begin
(
# 1488 "FStar.SMTEncoding.Encode.fst"
let _78_2499 = (encode_binders None formals env)
in (match (_78_2499) with
| (vars, guards, env', binder_decls, _78_2498) -> begin
(
# 1490 "FStar.SMTEncoding.Encode.fst"
let _78_2503 = (new_term_constant_and_tok_from_lid env t)
in (match (_78_2503) with
| (tname, ttok, env) -> begin
(
# 1491 "FStar.SMTEncoding.Encode.fst"
let ttok_tm = (FStar_SMTEncoding_Term.mkApp (ttok, []))
in (
# 1492 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1493 "FStar.SMTEncoding.Encode.fst"
let tapp = (let _162_1978 = (let _162_1977 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (tname, _162_1977))
in (FStar_SMTEncoding_Term.mkApp _162_1978))
in (
# 1494 "FStar.SMTEncoding.Encode.fst"
let _78_2524 = (
# 1495 "FStar.SMTEncoding.Encode.fst"
let tname_decl = (let _162_1982 = (let _162_1981 = (FStar_All.pipe_right vars (FStar_List.map (fun _78_2509 -> (match (_78_2509) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _162_1980 = (varops.next_id ())
in (tname, _162_1981, FStar_SMTEncoding_Term.Term_sort, _162_1980, false)))
in (constructor_or_logic_type_decl _162_1982))
in (
# 1496 "FStar.SMTEncoding.Encode.fst"
let _78_2521 = (match (vars) with
| [] -> begin
(let _162_1986 = (let _162_1985 = (let _162_1984 = (FStar_SMTEncoding_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _162_1983 -> Some (_162_1983)) _162_1984))
in (push_free_var env t tname _162_1985))
in ([], _162_1986))
end
| _78_2513 -> begin
(
# 1499 "FStar.SMTEncoding.Encode.fst"
let ttok_decl = FStar_SMTEncoding_Term.DeclFun ((ttok, [], FStar_SMTEncoding_Term.Term_sort, Some ("token")))
in (
# 1500 "FStar.SMTEncoding.Encode.fst"
let ttok_fresh = (let _162_1987 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ttok, FStar_SMTEncoding_Term.Term_sort) _162_1987))
in (
# 1501 "FStar.SMTEncoding.Encode.fst"
let ttok_app = (mk_Apply ttok_tm vars)
in (
# 1502 "FStar.SMTEncoding.Encode.fst"
let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (
# 1505 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _162_1991 = (let _162_1990 = (let _162_1989 = (let _162_1988 = (FStar_SMTEncoding_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _162_1988))
in (FStar_SMTEncoding_Term.mkForall' _162_1989))
in (_162_1990, Some ("name-token correspondence")))
in FStar_SMTEncoding_Term.Assume (_162_1991))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_78_2521) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_78_2524) with
| (decls, env) -> begin
(
# 1508 "FStar.SMTEncoding.Encode.fst"
let kindingAx = (
# 1509 "FStar.SMTEncoding.Encode.fst"
let _78_2527 = (encode_term_pred None res env' tapp)
in (match (_78_2527) with
| (k, decls) -> begin
(
# 1510 "FStar.SMTEncoding.Encode.fst"
let karr = if ((FStar_List.length formals) > 0) then begin
(let _162_1995 = (let _162_1994 = (let _162_1993 = (let _162_1992 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" _162_1992))
in (_162_1993, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_162_1994))
in (_162_1995)::[])
end else begin
[]
end
in (let _162_2001 = (let _162_2000 = (let _162_1999 = (let _162_1998 = (let _162_1997 = (let _162_1996 = (FStar_SMTEncoding_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _162_1996))
in (FStar_SMTEncoding_Term.mkForall _162_1997))
in (_162_1998, Some ("kinding")))
in FStar_SMTEncoding_Term.Assume (_162_1999))
in (_162_2000)::[])
in (FStar_List.append (FStar_List.append decls karr) _162_2001)))
end))
in (
# 1515 "FStar.SMTEncoding.Encode.fst"
let aux = (let _162_2005 = (let _162_2002 = (inversion_axioms tapp vars)
in (FStar_List.append kindingAx _162_2002))
in (let _162_2004 = (let _162_2003 = (pretype_axiom tapp vars)
in (_162_2003)::[])
in (FStar_List.append _162_2005 _162_2004)))
in (
# 1520 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, _78_2534, _78_2536, _78_2538, _78_2540, _78_2542, _78_2544, _78_2546) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Syntax_Syntax.Sig_datacon (d, _78_2551, t, _78_2554, n_tps, quals, _78_2558, drange) -> begin
(
# 1528 "FStar.SMTEncoding.Encode.fst"
let _78_2565 = (new_term_constant_and_tok_from_lid env d)
in (match (_78_2565) with
| (ddconstrsym, ddtok, env) -> begin
(
# 1529 "FStar.SMTEncoding.Encode.fst"
let ddtok_tm = (FStar_SMTEncoding_Term.mkApp (ddtok, []))
in (
# 1530 "FStar.SMTEncoding.Encode.fst"
let _78_2569 = (FStar_Syntax_Util.arrow_formals t)
in (match (_78_2569) with
| (formals, t_res) -> begin
(
# 1531 "FStar.SMTEncoding.Encode.fst"
let _78_2572 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (_78_2572) with
| (fuel_var, fuel_tm) -> begin
(
# 1532 "FStar.SMTEncoding.Encode.fst"
let s_fuel_tm = (FStar_SMTEncoding_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (
# 1533 "FStar.SMTEncoding.Encode.fst"
let _78_2579 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_78_2579) with
| (vars, guards, env', binder_decls, names) -> begin
(
# 1534 "FStar.SMTEncoding.Encode.fst"
let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (let _162_2007 = (mk_term_projector_name d x)
in (_162_2007, FStar_SMTEncoding_Term.Term_sort)))))
in (
# 1535 "FStar.SMTEncoding.Encode.fst"
let datacons = (let _162_2009 = (let _162_2008 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_SMTEncoding_Term.Term_sort, _162_2008, true))
in (FStar_All.pipe_right _162_2009 FStar_SMTEncoding_Term.constructor_to_decl))
in (
# 1536 "FStar.SMTEncoding.Encode.fst"
let app = (mk_Apply ddtok_tm vars)
in (
# 1537 "FStar.SMTEncoding.Encode.fst"
let guard = (FStar_SMTEncoding_Term.mk_and_l guards)
in (
# 1538 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1539 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1541 "FStar.SMTEncoding.Encode.fst"
let _78_2589 = (encode_term_pred None t env ddtok_tm)
in (match (_78_2589) with
| (tok_typing, decls3) -> begin
(
# 1543 "FStar.SMTEncoding.Encode.fst"
let _78_2596 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_78_2596) with
| (vars', guards', env'', decls_formals, _78_2595) -> begin
(
# 1544 "FStar.SMTEncoding.Encode.fst"
let _78_2601 = (
# 1545 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars')
in (
# 1546 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_78_2601) with
| (ty_pred', decls_pred) -> begin
(
# 1548 "FStar.SMTEncoding.Encode.fst"
let guard' = (FStar_SMTEncoding_Term.mk_and_l guards')
in (
# 1549 "FStar.SMTEncoding.Encode.fst"
let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _78_2605 -> begin
(let _162_2011 = (let _162_2010 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (ddtok, FStar_SMTEncoding_Term.Term_sort) _162_2010))
in (_162_2011)::[])
end)
in (
# 1553 "FStar.SMTEncoding.Encode.fst"
let encode_elim = (fun _78_2608 -> (match (()) with
| () -> begin
(
# 1554 "FStar.SMTEncoding.Encode.fst"
let _78_2611 = (FStar_Syntax_Util.head_and_args t_res)
in (match (_78_2611) with
| (head, args) -> begin
(match ((let _162_2014 = (FStar_Syntax_Subst.compress head)
in _162_2014.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(
# 1558 "FStar.SMTEncoding.Encode.fst"
let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (
# 1559 "FStar.SMTEncoding.Encode.fst"
let _78_2629 = (encode_args args env')
in (match (_78_2629) with
| (encoded_args, arg_decls) -> begin
(
# 1560 "FStar.SMTEncoding.Encode.fst"
let _78_2644 = (FStar_List.fold_left (fun _78_2633 arg -> (match (_78_2633) with
| (env, arg_vars, eqns) -> begin
(
# 1561 "FStar.SMTEncoding.Encode.fst"
let _78_2639 = (let _162_2017 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env _162_2017))
in (match (_78_2639) with
| (_78_2636, xv, env) -> begin
(let _162_2019 = (let _162_2018 = (FStar_SMTEncoding_Term.mkEq (arg, xv))
in (_162_2018)::eqns)
in (env, (xv)::arg_vars, _162_2019))
end))
end)) (env', [], []) encoded_args)
in (match (_78_2644) with
| (_78_2641, arg_vars, eqns) -> begin
(
# 1563 "FStar.SMTEncoding.Encode.fst"
let arg_vars = (FStar_List.rev arg_vars)
in (
# 1564 "FStar.SMTEncoding.Encode.fst"
let ty = (FStar_SMTEncoding_Term.mkApp (encoded_head, arg_vars))
in (
# 1565 "FStar.SMTEncoding.Encode.fst"
let xvars = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (
# 1566 "FStar.SMTEncoding.Encode.fst"
let dapp = (FStar_SMTEncoding_Term.mkApp (ddconstrsym, xvars))
in (
# 1567 "FStar.SMTEncoding.Encode.fst"
let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (
# 1568 "FStar.SMTEncoding.Encode.fst"
let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (
# 1569 "FStar.SMTEncoding.Encode.fst"
let typing_inversion = (let _162_2026 = (let _162_2025 = (let _162_2024 = (let _162_2023 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _162_2022 = (let _162_2021 = (let _162_2020 = (FStar_SMTEncoding_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _162_2020))
in (FStar_SMTEncoding_Term.mkImp _162_2021))
in (((ty_pred)::[])::[], _162_2023, _162_2022)))
in (FStar_SMTEncoding_Term.mkForall _162_2024))
in (_162_2025, Some ("data constructor typing elim")))
in FStar_SMTEncoding_Term.Assume (_162_2026))
in (
# 1574 "FStar.SMTEncoding.Encode.fst"
let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid) then begin
(
# 1576 "FStar.SMTEncoding.Encode.fst"
let x = (let _162_2027 = (varops.fresh "x")
in (_162_2027, FStar_SMTEncoding_Term.Term_sort))
in (
# 1577 "FStar.SMTEncoding.Encode.fst"
let xtm = (FStar_SMTEncoding_Term.mkFreeV x)
in (let _162_2037 = (let _162_2036 = (let _162_2035 = (let _162_2034 = (let _162_2029 = (let _162_2028 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_162_2028)::[])
in (_162_2029)::[])
in (let _162_2033 = (let _162_2032 = (let _162_2031 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (let _162_2030 = (FStar_SMTEncoding_Term.mk_Precedes xtm dapp)
in (_162_2031, _162_2030)))
in (FStar_SMTEncoding_Term.mkImp _162_2032))
in (_162_2034, (x)::[], _162_2033)))
in (FStar_SMTEncoding_Term.mkForall _162_2035))
in (_162_2036, Some ("lextop is top")))
in FStar_SMTEncoding_Term.Assume (_162_2037))))
end else begin
(
# 1580 "FStar.SMTEncoding.Encode.fst"
let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(let _162_2040 = (let _162_2039 = (FStar_SMTEncoding_Term.mkFreeV v)
in (FStar_SMTEncoding_Term.mk_Precedes _162_2039 dapp))
in (_162_2040)::[])
end
| _78_2658 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _162_2047 = (let _162_2046 = (let _162_2045 = (let _162_2044 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _162_2043 = (let _162_2042 = (let _162_2041 = (FStar_SMTEncoding_Term.mk_and_l prec)
in (ty_pred, _162_2041))
in (FStar_SMTEncoding_Term.mkImp _162_2042))
in (((ty_pred)::[])::[], _162_2044, _162_2043)))
in (FStar_SMTEncoding_Term.mkForall _162_2045))
in (_162_2046, Some ("subterm ordering")))
in FStar_SMTEncoding_Term.Assume (_162_2047)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _78_2662 -> begin
(
# 1588 "FStar.SMTEncoding.Encode.fst"
let _78_2663 = (let _162_2050 = (let _162_2049 = (FStar_Syntax_Print.lid_to_string d)
in (let _162_2048 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _162_2049 _162_2048)))
in (FStar_TypeChecker_Errors.warn drange _162_2050))
in ([], []))
end)
end))
end))
in (
# 1591 "FStar.SMTEncoding.Encode.fst"
let _78_2667 = (encode_elim ())
in (match (_78_2667) with
| (decls2, elim) -> begin
(
# 1592 "FStar.SMTEncoding.Encode.fst"
let g = (let _162_2075 = (let _162_2074 = (let _162_2059 = (let _162_2058 = (let _162_2057 = (let _162_2056 = (let _162_2055 = (let _162_2054 = (let _162_2053 = (let _162_2052 = (let _162_2051 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" _162_2051))
in Some (_162_2052))
in (ddtok, [], FStar_SMTEncoding_Term.Term_sort, _162_2053))
in FStar_SMTEncoding_Term.DeclFun (_162_2054))
in (_162_2055)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _162_2056))
in (FStar_List.append _162_2057 proxy_fresh))
in (FStar_List.append _162_2058 decls_formals))
in (FStar_List.append _162_2059 decls_pred))
in (let _162_2073 = (let _162_2072 = (let _162_2071 = (let _162_2063 = (let _162_2062 = (let _162_2061 = (let _162_2060 = (FStar_SMTEncoding_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _162_2060))
in (FStar_SMTEncoding_Term.mkForall _162_2061))
in (_162_2062, Some ("equality for proxy")))
in FStar_SMTEncoding_Term.Assume (_162_2063))
in (let _162_2070 = (let _162_2069 = (let _162_2068 = (let _162_2067 = (let _162_2066 = (let _162_2065 = (add_fuel (fuel_var, FStar_SMTEncoding_Term.Fuel_sort) vars')
in (let _162_2064 = (FStar_SMTEncoding_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _162_2065, _162_2064)))
in (FStar_SMTEncoding_Term.mkForall _162_2066))
in (_162_2067, Some ("data constructor typing intro")))
in FStar_SMTEncoding_Term.Assume (_162_2068))
in (_162_2069)::[])
in (_162_2071)::_162_2070))
in (FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_162_2072)
in (FStar_List.append _162_2074 _162_2073)))
in (FStar_List.append _162_2075 elim))
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
and declare_top_level_let : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * FStar_SMTEncoding_Term.term Prims.option) * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (match ((try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)) with
| None -> begin
(
# 1610 "FStar.SMTEncoding.Encode.fst"
let _78_2676 = (encode_free_var env x t t_norm [])
in (match (_78_2676) with
| (decls, env) -> begin
(
# 1611 "FStar.SMTEncoding.Encode.fst"
let _78_2681 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (_78_2681) with
| (n, x', _78_2680) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _78_2685) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (
# 1617 "FStar.SMTEncoding.Encode.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (
# 1618 "FStar.SMTEncoding.Encode.fst"
let _78_2694 = (encode_function_type_as_formula None None t env)
in (match (_78_2694) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)))))::[]))
end))))
and encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (
# 1622 "FStar.SMTEncoding.Encode.fst"
let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in if ((let _162_2088 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _162_2088)) || (FStar_Syntax_Util.is_lemma t_norm)) then begin
(
# 1625 "FStar.SMTEncoding.Encode.fst"
let _78_2704 = (new_term_constant_and_tok_from_lid env lid)
in (match (_78_2704) with
| (vname, vtok, env) -> begin
(
# 1626 "FStar.SMTEncoding.Encode.fst"
let arg_sorts = (match ((let _162_2089 = (FStar_Syntax_Subst.compress t_norm)
in _162_2089.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_arrow (binders, _78_2707) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _78_2710 -> FStar_SMTEncoding_Term.Term_sort)))
end
| _78_2713 -> begin
[]
end)
in (
# 1629 "FStar.SMTEncoding.Encode.fst"
let d = FStar_SMTEncoding_Term.DeclFun ((vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (
# 1630 "FStar.SMTEncoding.Encode.fst"
let dd = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(
# 1633 "FStar.SMTEncoding.Encode.fst"
let vname = (varops.new_fvar lid)
in (
# 1634 "FStar.SMTEncoding.Encode.fst"
let definition = (prims.mk lid vname)
in (
# 1635 "FStar.SMTEncoding.Encode.fst"
let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(
# 1637 "FStar.SMTEncoding.Encode.fst"
let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (
# 1638 "FStar.SMTEncoding.Encode.fst"
let _78_2728 = (
# 1639 "FStar.SMTEncoding.Encode.fst"
let _78_2723 = (curried_arrow_formals_comp t_norm)
in (match (_78_2723) with
| (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _162_2091 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _162_2091))
end else begin
(args, (None, (FStar_Syntax_Util.comp_result comp)))
end
end))
in (match (_78_2728) with
| (formals, (pre_opt, res_t)) -> begin
(
# 1643 "FStar.SMTEncoding.Encode.fst"
let _78_2732 = (new_term_constant_and_tok_from_lid env lid)
in (match (_78_2732) with
| (vname, vtok, env) -> begin
(
# 1644 "FStar.SMTEncoding.Encode.fst"
let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
end
| _78_2735 -> begin
(FStar_SMTEncoding_Term.mkApp (vtok, []))
end)
in (
# 1647 "FStar.SMTEncoding.Encode.fst"
let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _78_20 -> (match (_78_20) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(
# 1649 "FStar.SMTEncoding.Encode.fst"
let _78_2751 = (FStar_Util.prefix vars)
in (match (_78_2751) with
| (_78_2746, (xxsym, _78_2749)) -> begin
(
# 1650 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (let _162_2108 = (let _162_2107 = (let _162_2106 = (let _162_2105 = (let _162_2104 = (let _162_2103 = (let _162_2102 = (let _162_2101 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool _162_2101))
in (vapp, _162_2102))
in (FStar_SMTEncoding_Term.mkEq _162_2103))
in (((vapp)::[])::[], vars, _162_2104))
in (FStar_SMTEncoding_Term.mkForall _162_2105))
in (_162_2106, Some ("Discriminator equation")))
in FStar_SMTEncoding_Term.Assume (_162_2107))
in (_162_2108)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(
# 1655 "FStar.SMTEncoding.Encode.fst"
let _78_2763 = (FStar_Util.prefix vars)
in (match (_78_2763) with
| (_78_2758, (xxsym, _78_2761)) -> begin
(
# 1656 "FStar.SMTEncoding.Encode.fst"
let xx = (FStar_SMTEncoding_Term.mkFreeV (xxsym, FStar_SMTEncoding_Term.Term_sort))
in (
# 1657 "FStar.SMTEncoding.Encode.fst"
let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = 0; FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (
# 1658 "FStar.SMTEncoding.Encode.fst"
let prim_app = (let _162_2110 = (let _162_2109 = (mk_term_projector_name d f)
in (_162_2109, (xx)::[]))
in (FStar_SMTEncoding_Term.mkApp _162_2110))
in (let _162_2115 = (let _162_2114 = (let _162_2113 = (let _162_2112 = (let _162_2111 = (FStar_SMTEncoding_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _162_2111))
in (FStar_SMTEncoding_Term.mkForall _162_2112))
in (_162_2113, Some ("Projector equation")))
in FStar_SMTEncoding_Term.Assume (_162_2114))
in (_162_2115)::[]))))
end))
end
| _78_2768 -> begin
[]
end)))))
in (
# 1662 "FStar.SMTEncoding.Encode.fst"
let _78_2775 = (encode_binders None formals env)
in (match (_78_2775) with
| (vars, guards, env', decls1, _78_2774) -> begin
(
# 1663 "FStar.SMTEncoding.Encode.fst"
let _78_2784 = (match (pre_opt) with
| None -> begin
(let _162_2116 = (FStar_SMTEncoding_Term.mk_and_l guards)
in (_162_2116, decls1))
end
| Some (p) -> begin
(
# 1665 "FStar.SMTEncoding.Encode.fst"
let _78_2781 = (encode_formula p env')
in (match (_78_2781) with
| (g, ds) -> begin
(let _162_2117 = (FStar_SMTEncoding_Term.mk_and_l ((g)::guards))
in (_162_2117, (FStar_List.append decls1 ds)))
end))
end)
in (match (_78_2784) with
| (guard, decls1) -> begin
(
# 1666 "FStar.SMTEncoding.Encode.fst"
let vtok_app = (mk_Apply vtok_tm vars)
in (
# 1668 "FStar.SMTEncoding.Encode.fst"
let vapp = (let _162_2119 = (let _162_2118 = (FStar_List.map FStar_SMTEncoding_Term.mkFreeV vars)
in (vname, _162_2118))
in (FStar_SMTEncoding_Term.mkApp _162_2119))
in (
# 1669 "FStar.SMTEncoding.Encode.fst"
let _78_2808 = (
# 1670 "FStar.SMTEncoding.Encode.fst"
let vname_decl = (let _162_2122 = (let _162_2121 = (FStar_All.pipe_right formals (FStar_List.map (fun _78_2787 -> FStar_SMTEncoding_Term.Term_sort)))
in (vname, _162_2121, FStar_SMTEncoding_Term.Term_sort, None))
in FStar_SMTEncoding_Term.DeclFun (_162_2122))
in (
# 1671 "FStar.SMTEncoding.Encode.fst"
let _78_2795 = (
# 1672 "FStar.SMTEncoding.Encode.fst"
let env = (
# 1672 "FStar.SMTEncoding.Encode.fst"
let _78_2790 = env
in {bindings = _78_2790.bindings; depth = _78_2790.depth; tcenv = _78_2790.tcenv; warn = _78_2790.warn; cache = _78_2790.cache; nolabels = _78_2790.nolabels; use_zfuel_name = _78_2790.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_term_pred None tt env vtok_tm)
end else begin
(encode_term_pred None t_norm env vtok_tm)
end)
in (match (_78_2795) with
| (tok_typing, decls2) -> begin
(
# 1676 "FStar.SMTEncoding.Encode.fst"
let tok_typing = FStar_SMTEncoding_Term.Assume ((tok_typing, Some ("function token typing")))
in (
# 1677 "FStar.SMTEncoding.Encode.fst"
let _78_2805 = (match (formals) with
| [] -> begin
(let _162_2126 = (let _162_2125 = (let _162_2124 = (FStar_SMTEncoding_Term.mkFreeV (vname, FStar_SMTEncoding_Term.Term_sort))
in (FStar_All.pipe_left (fun _162_2123 -> Some (_162_2123)) _162_2124))
in (push_free_var env lid vname _162_2125))
in ((FStar_List.append decls2 ((tok_typing)::[])), _162_2126))
end
| _78_2799 -> begin
(
# 1680 "FStar.SMTEncoding.Encode.fst"
let vtok_decl = FStar_SMTEncoding_Term.DeclFun ((vtok, [], FStar_SMTEncoding_Term.Term_sort, None))
in (
# 1681 "FStar.SMTEncoding.Encode.fst"
let vtok_fresh = (let _162_2127 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token (vtok, FStar_SMTEncoding_Term.Term_sort) _162_2127))
in (
# 1682 "FStar.SMTEncoding.Encode.fst"
let name_tok_corr = (let _162_2131 = (let _162_2130 = (let _162_2129 = (let _162_2128 = (FStar_SMTEncoding_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _162_2128))
in (FStar_SMTEncoding_Term.mkForall _162_2129))
in (_162_2130, None))
in FStar_SMTEncoding_Term.Assume (_162_2131))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_78_2805) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_78_2808) with
| (decls2, env) -> begin
(
# 1685 "FStar.SMTEncoding.Encode.fst"
let _78_2816 = (
# 1686 "FStar.SMTEncoding.Encode.fst"
let res_t = (FStar_Syntax_Subst.compress res_t)
in (
# 1687 "FStar.SMTEncoding.Encode.fst"
let _78_2812 = (encode_term res_t env')
in (match (_78_2812) with
| (encoded_res_t, decls) -> begin
(let _162_2132 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _162_2132, decls))
end)))
in (match (_78_2816) with
| (encoded_res_t, ty_pred, decls3) -> begin
(
# 1689 "FStar.SMTEncoding.Encode.fst"
let typingAx = (let _162_2136 = (let _162_2135 = (let _162_2134 = (let _162_2133 = (FStar_SMTEncoding_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _162_2133))
in (FStar_SMTEncoding_Term.mkForall _162_2134))
in (_162_2135, Some ("free var typing")))
in FStar_SMTEncoding_Term.Assume (_162_2136))
in (
# 1690 "FStar.SMTEncoding.Encode.fst"
let freshness = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New)) then begin
(let _162_2142 = (let _162_2139 = (let _162_2138 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _162_2137 = (varops.next_id ())
in (vname, _162_2138, FStar_SMTEncoding_Term.Term_sort, _162_2137)))
in (FStar_SMTEncoding_Term.fresh_constructor _162_2139))
in (let _162_2141 = (let _162_2140 = (pretype_axiom vapp vars)
in (_162_2140)::[])
in (_162_2142)::_162_2141))
end else begin
[]
end
in (
# 1695 "FStar.SMTEncoding.Encode.fst"
let g = (let _162_2144 = (let _162_2143 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_162_2143)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) freshness) _162_2144))
in (g, env))))
end))
end))))
end))
end))))
end))
end)))
end
end))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _78_2824 se -> (match (_78_2824) with
| (g, env) -> begin
(
# 1701 "FStar.SMTEncoding.Encode.fst"
let _78_2828 = (encode_sigelt env se)
in (match (_78_2828) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

# 1704 "FStar.SMTEncoding.Encode.fst"
let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings -> (
# 1729 "FStar.SMTEncoding.Encode.fst"
let encode_binding = (fun b _78_2835 -> (match (_78_2835) with
| (decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (_78_2837) -> begin
([], env)
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(
# 1734 "FStar.SMTEncoding.Encode.fst"
let _78_2844 = (new_term_constant env x)
in (match (_78_2844) with
| (xxsym, xx, env') -> begin
(
# 1735 "FStar.SMTEncoding.Encode.fst"
let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (
# 1736 "FStar.SMTEncoding.Encode.fst"
let _78_2846 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _162_2159 = (FStar_Syntax_Print.bv_to_string x)
in (let _162_2158 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _162_2157 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _162_2159 _162_2158 _162_2157))))
end else begin
()
end
in (
# 1738 "FStar.SMTEncoding.Encode.fst"
let _78_2850 = (encode_term_pred None t1 env xx)
in (match (_78_2850) with
| (t, decls') -> begin
(
# 1739 "FStar.SMTEncoding.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _162_2163 = (let _162_2162 = (FStar_Syntax_Print.bv_to_string x)
in (let _162_2161 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (let _162_2160 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _162_2162 _162_2161 _162_2160))))
in Some (_162_2163))
end else begin
None
end
in (
# 1743 "FStar.SMTEncoding.Encode.fst"
let g = (FStar_List.append (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun ((xxsym, [], FStar_SMTEncoding_Term.Term_sort, caption)))::[]) decls') ((FStar_SMTEncoding_Term.Assume ((t, None)))::[]))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_TypeChecker_Env.Binding_lid (x, (_78_2855, t)) -> begin
(
# 1749 "FStar.SMTEncoding.Encode.fst"
let t_norm = (whnf env t)
in (
# 1750 "FStar.SMTEncoding.Encode.fst"
let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (
# 1752 "FStar.SMTEncoding.Encode.fst"
let _78_2864 = (encode_free_var env fv t t_norm [])
in (match (_78_2864) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(
# 1757 "FStar.SMTEncoding.Encode.fst"
let _78_2878 = (encode_sigelt env se)
in (match (_78_2878) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

# 1762 "FStar.SMTEncoding.Encode.fst"
let encode_labels = (fun labs -> (
# 1763 "FStar.SMTEncoding.Encode.fst"
let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _78_2885 -> (match (_78_2885) with
| (l, _78_2882, _78_2884) -> begin
FStar_SMTEncoding_Term.DeclFun (((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))
end))))
in (
# 1764 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _78_2892 -> (match (_78_2892) with
| (l, _78_2889, _78_2891) -> begin
(let _162_2171 = (FStar_All.pipe_left (fun _162_2167 -> FStar_SMTEncoding_Term.Echo (_162_2167)) (Prims.fst l))
in (let _162_2170 = (let _162_2169 = (let _162_2168 = (FStar_SMTEncoding_Term.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (_162_2168))
in (_162_2169)::[])
in (_162_2171)::_162_2170))
end))))
in (prefix, suffix))))

# 1768 "FStar.SMTEncoding.Encode.fst"
let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 1769 "FStar.SMTEncoding.Encode.fst"
let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (let _162_2176 = (let _162_2175 = (let _162_2174 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _162_2174; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_162_2175)::[])
in (FStar_ST.op_Colon_Equals last_env _162_2176)))

# 1772 "FStar.SMTEncoding.Encode.fst"
let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_78_2898 -> begin
(
# 1774 "FStar.SMTEncoding.Encode.fst"
let _78_2901 = e
in {bindings = _78_2901.bindings; depth = _78_2901.depth; tcenv = tcenv; warn = _78_2901.warn; cache = _78_2901.cache; nolabels = _78_2901.nolabels; use_zfuel_name = _78_2901.use_zfuel_name; encode_non_total_function_typ = _78_2901.encode_non_total_function_typ})
end))

# 1775 "FStar.SMTEncoding.Encode.fst"
let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _78_2907::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

# 1778 "FStar.SMTEncoding.Encode.fst"
let push_env : Prims.unit  ->  Prims.unit = (fun _78_2909 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(
# 1781 "FStar.SMTEncoding.Encode.fst"
let refs = (FStar_Util.smap_copy hd.cache)
in (
# 1782 "FStar.SMTEncoding.Encode.fst"
let top = (
# 1782 "FStar.SMTEncoding.Encode.fst"
let _78_2915 = hd
in {bindings = _78_2915.bindings; depth = _78_2915.depth; tcenv = _78_2915.tcenv; warn = _78_2915.warn; cache = refs; nolabels = _78_2915.nolabels; use_zfuel_name = _78_2915.use_zfuel_name; encode_non_total_function_typ = _78_2915.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

# 1784 "FStar.SMTEncoding.Encode.fst"
let pop_env : Prims.unit  ->  Prims.unit = (fun _78_2918 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _78_2922::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

# 1787 "FStar.SMTEncoding.Encode.fst"
let mark_env : Prims.unit  ->  Prims.unit = (fun _78_2924 -> (match (()) with
| () -> begin
(push_env ())
end))

# 1788 "FStar.SMTEncoding.Encode.fst"
let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _78_2925 -> (match (()) with
| () -> begin
(pop_env ())
end))

# 1789 "FStar.SMTEncoding.Encode.fst"
let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _78_2926 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_78_2929::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _78_2934 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 1795 "FStar.SMTEncoding.Encode.fst"
let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (
# 1796 "FStar.SMTEncoding.Encode.fst"
let _78_2936 = (init_env tcenv)
in (
# 1797 "FStar.SMTEncoding.Encode.fst"
let _78_2938 = (FStar_SMTEncoding_Z3.init ())
in (FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[])))))

# 1799 "FStar.SMTEncoding.Encode.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 1800 "FStar.SMTEncoding.Encode.fst"
let _78_2941 = (push_env ())
in (
# 1801 "FStar.SMTEncoding.Encode.fst"
let _78_2943 = (varops.push ())
in (FStar_SMTEncoding_Z3.push msg))))

# 1803 "FStar.SMTEncoding.Encode.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 1804 "FStar.SMTEncoding.Encode.fst"
let _78_2946 = (let _162_2197 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _162_2197))
in (
# 1805 "FStar.SMTEncoding.Encode.fst"
let _78_2948 = (varops.pop ())
in (FStar_SMTEncoding_Z3.pop msg))))

# 1807 "FStar.SMTEncoding.Encode.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1808 "FStar.SMTEncoding.Encode.fst"
let _78_2951 = (mark_env ())
in (
# 1809 "FStar.SMTEncoding.Encode.fst"
let _78_2953 = (varops.mark ())
in (FStar_SMTEncoding_Z3.mark msg))))

# 1811 "FStar.SMTEncoding.Encode.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 1812 "FStar.SMTEncoding.Encode.fst"
let _78_2956 = (reset_mark_env ())
in (
# 1813 "FStar.SMTEncoding.Encode.fst"
let _78_2958 = (varops.reset_mark ())
in (FStar_SMTEncoding_Z3.reset_mark msg))))

# 1815 "FStar.SMTEncoding.Encode.fst"
let commit_mark = (fun msg -> (
# 1816 "FStar.SMTEncoding.Encode.fst"
let _78_2961 = (commit_mark_env ())
in (
# 1817 "FStar.SMTEncoding.Encode.fst"
let _78_2963 = (varops.commit_mark ())
in (FStar_SMTEncoding_Z3.commit_mark msg))))

# 1819 "FStar.SMTEncoding.Encode.fst"
let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (
# 1820 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _162_2213 = (let _162_2212 = (let _162_2211 = (let _162_2210 = (let _162_2209 = (FStar_Syntax_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _162_2209 (FStar_List.map FStar_Syntax_Print.lid_to_string)))
in (FStar_All.pipe_right _162_2210 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " _162_2211))
in FStar_SMTEncoding_Term.Caption (_162_2212))
in (_162_2213)::decls)
end else begin
decls
end)
in (
# 1824 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1825 "FStar.SMTEncoding.Encode.fst"
let _78_2972 = (encode_sigelt env se)
in (match (_78_2972) with
| (decls, env) -> begin
(
# 1826 "FStar.SMTEncoding.Encode.fst"
let _78_2973 = (set_env env)
in (let _162_2214 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 _162_2214)))
end)))))

# 1829 "FStar.SMTEncoding.Encode.fst"
let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (
# 1830 "FStar.SMTEncoding.Encode.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Syntax_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (
# 1831 "FStar.SMTEncoding.Encode.fst"
let _78_2978 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(let _162_2219 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name _162_2219))
end else begin
()
end
in (
# 1833 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1834 "FStar.SMTEncoding.Encode.fst"
let _78_2985 = (encode_signature (
# 1834 "FStar.SMTEncoding.Encode.fst"
let _78_2981 = env
in {bindings = _78_2981.bindings; depth = _78_2981.depth; tcenv = _78_2981.tcenv; warn = false; cache = _78_2981.cache; nolabels = _78_2981.nolabels; use_zfuel_name = _78_2981.use_zfuel_name; encode_non_total_function_typ = _78_2981.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (_78_2985) with
| (decls, env) -> begin
(
# 1835 "FStar.SMTEncoding.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(
# 1837 "FStar.SMTEncoding.Encode.fst"
let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (
# 1840 "FStar.SMTEncoding.Encode.fst"
let _78_2991 = (set_env (
# 1840 "FStar.SMTEncoding.Encode.fst"
let _78_2989 = env
in {bindings = _78_2989.bindings; depth = _78_2989.depth; tcenv = _78_2989.tcenv; warn = true; cache = _78_2989.cache; nolabels = _78_2989.nolabels; use_zfuel_name = _78_2989.use_zfuel_name; encode_non_total_function_typ = _78_2989.encode_non_total_function_typ}))
in (
# 1841 "FStar.SMTEncoding.Encode.fst"
let _78_2993 = if (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (
# 1842 "FStar.SMTEncoding.Encode.fst"
let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls)))))
end))))))

# 1845 "FStar.SMTEncoding.Encode.fst"
let solve : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun use_env_msg tcenv q -> (
# 1846 "FStar.SMTEncoding.Encode.fst"
let _78_2999 = (let _162_2238 = (let _162_2237 = (let _162_2236 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _162_2236))
in (FStar_Util.format1 "Starting query at %s" _162_2237))
in (push _162_2238))
in (
# 1847 "FStar.SMTEncoding.Encode.fst"
let pop = (fun _78_3002 -> (match (()) with
| () -> begin
(let _162_2243 = (let _162_2242 = (let _162_2241 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _162_2241))
in (FStar_Util.format1 "Ending query at %s" _162_2242))
in (pop _162_2243))
end))
in (
# 1848 "FStar.SMTEncoding.Encode.fst"
let _78_3056 = (
# 1849 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1850 "FStar.SMTEncoding.Encode.fst"
let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (
# 1851 "FStar.SMTEncoding.Encode.fst"
let _78_3026 = (
# 1852 "FStar.SMTEncoding.Encode.fst"
let rec aux = (fun bindings -> (match (bindings) with
| FStar_TypeChecker_Env.Binding_var (x)::rest -> begin
(
# 1854 "FStar.SMTEncoding.Encode.fst"
let _78_3015 = (aux rest)
in (match (_78_3015) with
| (out, rest) -> begin
(
# 1855 "FStar.SMTEncoding.Encode.fst"
let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (let _162_2249 = (let _162_2248 = (FStar_Syntax_Syntax.mk_binder (
# 1856 "FStar.SMTEncoding.Encode.fst"
let _78_3017 = x
in {FStar_Syntax_Syntax.ppname = _78_3017.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _78_3017.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (_162_2248)::out)
in (_162_2249, rest)))
end))
end
| _78_3020 -> begin
([], bindings)
end))
in (
# 1858 "FStar.SMTEncoding.Encode.fst"
let _78_3023 = (aux bindings)
in (match (_78_3023) with
| (closing, bindings) -> begin
(let _162_2250 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in (_162_2250, bindings))
end)))
in (match (_78_3026) with
| (q, bindings) -> begin
(
# 1860 "FStar.SMTEncoding.Encode.fst"
let _78_3035 = (let _162_2252 = (FStar_List.filter (fun _78_21 -> (match (_78_21) with
| FStar_TypeChecker_Env.Binding_sig (_78_3029) -> begin
false
end
| _78_3032 -> begin
true
end)) bindings)
in (encode_env_bindings env _162_2252))
in (match (_78_3035) with
| (env_decls, env) -> begin
(
# 1861 "FStar.SMTEncoding.Encode.fst"
let _78_3036 = if ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) then begin
(let _162_2253 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _162_2253))
end else begin
()
end
in (
# 1864 "FStar.SMTEncoding.Encode.fst"
let _78_3040 = (encode_formula q env)
in (match (_78_3040) with
| (phi, qdecls) -> begin
(
# 1867 "FStar.SMTEncoding.Encode.fst"
let _78_3045 = (let _162_2254 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg _162_2254 phi))
in (match (_78_3045) with
| (phi, labels, _78_3044) -> begin
(
# 1868 "FStar.SMTEncoding.Encode.fst"
let _78_3048 = (encode_labels labels)
in (match (_78_3048) with
| (label_prefix, label_suffix) -> begin
(
# 1869 "FStar.SMTEncoding.Encode.fst"
let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (
# 1873 "FStar.SMTEncoding.Encode.fst"
let qry = (let _162_2256 = (let _162_2255 = (FStar_SMTEncoding_Term.mkNot phi)
in (_162_2255, Some ("query")))
in FStar_SMTEncoding_Term.Assume (_162_2256))
in (
# 1874 "FStar.SMTEncoding.Encode.fst"
let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end))
end)))
end))
end))))
in (match (_78_3056) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _78_3063); FStar_SMTEncoding_Term.hash = _78_3060; FStar_SMTEncoding_Term.freevars = _78_3058}, _78_3068) -> begin
(
# 1877 "FStar.SMTEncoding.Encode.fst"
let _78_3071 = (pop ())
in ())
end
| _78_3074 when tcenv.FStar_TypeChecker_Env.admit -> begin
(
# 1878 "FStar.SMTEncoding.Encode.fst"
let _78_3075 = (pop ())
in ())
end
| FStar_SMTEncoding_Term.Assume (q, _78_3079) -> begin
(
# 1880 "FStar.SMTEncoding.Encode.fst"
let fresh = ((FStar_String.length q.FStar_SMTEncoding_Term.hash) >= 2048)
in (
# 1881 "FStar.SMTEncoding.Encode.fst"
let _78_3083 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (
# 1883 "FStar.SMTEncoding.Encode.fst"
let with_fuel = (fun p _78_3089 -> (match (_78_3089) with
| (n, i) -> begin
(let _162_2279 = (let _162_2278 = (let _162_2263 = (let _162_2262 = (FStar_Util.string_of_int n)
in (let _162_2261 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _162_2262 _162_2261)))
in FStar_SMTEncoding_Term.Caption (_162_2263))
in (let _162_2277 = (let _162_2276 = (let _162_2268 = (let _162_2267 = (let _162_2266 = (let _162_2265 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _162_2264 = (FStar_SMTEncoding_Term.n_fuel n)
in (_162_2265, _162_2264)))
in (FStar_SMTEncoding_Term.mkEq _162_2266))
in (_162_2267, None))
in FStar_SMTEncoding_Term.Assume (_162_2268))
in (let _162_2275 = (let _162_2274 = (let _162_2273 = (let _162_2272 = (let _162_2271 = (let _162_2270 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _162_2269 = (FStar_SMTEncoding_Term.n_fuel i)
in (_162_2270, _162_2269)))
in (FStar_SMTEncoding_Term.mkEq _162_2271))
in (_162_2272, None))
in FStar_SMTEncoding_Term.Assume (_162_2273))
in (_162_2274)::(p)::(FStar_SMTEncoding_Term.CheckSat)::[])
in (_162_2276)::_162_2275))
in (_162_2278)::_162_2277))
in (FStar_List.append _162_2279 suffix))
end))
in (
# 1890 "FStar.SMTEncoding.Encode.fst"
let check = (fun p -> (
# 1891 "FStar.SMTEncoding.Encode.fst"
let initial_config = (let _162_2283 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _162_2282 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_162_2283, _162_2282)))
in (
# 1892 "FStar.SMTEncoding.Encode.fst"
let alt_configs = (let _162_2302 = (let _162_2301 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _162_2286 = (let _162_2285 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _162_2284 = (FStar_ST.read FStar_Options.max_ifuel)
in (_162_2285, _162_2284)))
in (_162_2286)::[])
end else begin
[]
end
in (let _162_2300 = (let _162_2299 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _162_2289 = (let _162_2288 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _162_2287 = (FStar_ST.read FStar_Options.max_ifuel)
in (_162_2288, _162_2287)))
in (_162_2289)::[])
end else begin
[]
end
in (let _162_2298 = (let _162_2297 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _162_2292 = (let _162_2291 = (FStar_ST.read FStar_Options.max_fuel)
in (let _162_2290 = (FStar_ST.read FStar_Options.max_ifuel)
in (_162_2291, _162_2290)))
in (_162_2292)::[])
end else begin
[]
end
in (let _162_2296 = (let _162_2295 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _162_2294 = (let _162_2293 = (FStar_ST.read FStar_Options.min_fuel)
in (_162_2293, 1))
in (_162_2294)::[])
end else begin
[]
end
in (_162_2295)::[])
in (_162_2297)::_162_2296))
in (_162_2299)::_162_2298))
in (_162_2301)::_162_2300))
in (FStar_List.flatten _162_2302))
in (
# 1897 "FStar.SMTEncoding.Encode.fst"
let report = (fun errs -> (
# 1898 "FStar.SMTEncoding.Encode.fst"
let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Range.dummyRange))::[]
end
| _78_3098 -> begin
errs
end)
in (
# 1901 "FStar.SMTEncoding.Encode.fst"
let _78_3100 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _162_2310 = (let _162_2305 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_Range.string_of_range _162_2305))
in (let _162_2309 = (let _162_2306 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _162_2306 FStar_Util.string_of_int))
in (let _162_2308 = (let _162_2307 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _162_2307 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _162_2310 _162_2309 _162_2308))))
end else begin
()
end
in (FStar_TypeChecker_Errors.add_errors tcenv errs))))
in (
# 1908 "FStar.SMTEncoding.Encode.fst"
let rec try_alt_configs = (fun p errs _78_22 -> (match (_78_22) with
| [] -> begin
(report errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _162_2321 = (with_fuel p mi)
in (FStar_SMTEncoding_Z3.ask fresh labels _162_2321 (cb mi p [])))
end
| _78_3112 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _162_2323 = (with_fuel p mi)
in (FStar_SMTEncoding_Z3.ask fresh labels _162_2323 (fun _78_3118 -> (match (_78_3118) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _78_3121 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _78_3124 p alt _78_3129 -> (match ((_78_3124, _78_3129)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _162_2331 = (let _162_2328 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_Range.string_of_range _162_2328))
in (let _162_2330 = (FStar_Util.string_of_int prev_fuel)
in (let _162_2329 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _162_2331 _162_2330 _162_2329))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _162_2332 = (with_fuel p initial_config)
in (FStar_SMTEncoding_Z3.ask fresh labels _162_2332 (cb initial_config p alt_configs))))))))
in (
# 1933 "FStar.SMTEncoding.Encode.fst"
let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 1935 "FStar.SMTEncoding.Encode.fst"
let _78_3134 = (let _162_2338 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _162_2338 q))
in (match (_78_3134) with
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
# 1940 "FStar.SMTEncoding.Encode.fst"
let _78_3135 = if (FStar_ST.read FStar_Options.admit_smt_queries) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end
| _78_3138 -> begin
(FStar_All.failwith "Impossible")
end)
end)))))

# 1946 "FStar.SMTEncoding.Encode.fst"
let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (
# 1947 "FStar.SMTEncoding.Encode.fst"
let env = (get_env tcenv)
in (
# 1948 "FStar.SMTEncoding.Encode.fst"
let _78_3142 = (push "query")
in (
# 1949 "FStar.SMTEncoding.Encode.fst"
let _78_3149 = (encode_formula_with_labels q env)
in (match (_78_3149) with
| (f, _78_3146, _78_3148) -> begin
(
# 1950 "FStar.SMTEncoding.Encode.fst"
let _78_3150 = (pop "query")
in (match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _78_3154) -> begin
true
end
| _78_3158 -> begin
false
end))
end)))))

# 1955 "FStar.SMTEncoding.Encode.fst"
let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = init; FStar_TypeChecker_Env.push = push; FStar_TypeChecker_Env.pop = pop; FStar_TypeChecker_Env.mark = mark; FStar_TypeChecker_Env.reset_mark = reset_mark; FStar_TypeChecker_Env.commit_mark = commit_mark; FStar_TypeChecker_Env.encode_modul = encode_modul; FStar_TypeChecker_Env.encode_sig = encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}

# 1969 "FStar.SMTEncoding.Encode.fst"
let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun _78_3159 -> ()); FStar_TypeChecker_Env.push = (fun _78_3161 -> ()); FStar_TypeChecker_Env.pop = (fun _78_3163 -> ()); FStar_TypeChecker_Env.mark = (fun _78_3165 -> ()); FStar_TypeChecker_Env.reset_mark = (fun _78_3167 -> ()); FStar_TypeChecker_Env.commit_mark = (fun _78_3169 -> ()); FStar_TypeChecker_Env.encode_modul = (fun _78_3171 _78_3173 -> ()); FStar_TypeChecker_Env.encode_sig = (fun _78_3175 _78_3177 -> ()); FStar_TypeChecker_Env.solve = (fun _78_3179 _78_3181 _78_3183 -> ()); FStar_TypeChecker_Env.is_trivial = (fun _78_3185 _78_3187 -> false); FStar_TypeChecker_Env.finish = (fun _78_3189 -> ()); FStar_TypeChecker_Env.refresh = (fun _78_3190 -> ())}






open Prims
# 31 "FStar.ToSMT.Encode.fst"
let add_fuel = (fun x tl -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
tl
end else begin
(x)::tl
end)

# 32 "FStar.ToSMT.Encode.fst"
let withenv = (fun c _50_39 -> (match (_50_39) with
| (a, b) -> begin
(a, b, c)
end))

# 33 "FStar.ToSMT.Encode.fst"
let vargs = (fun args -> (FStar_List.filter (fun _50_1 -> (match (_50_1) with
| (FStar_Util.Inl (_50_43), _50_46) -> begin
false
end
| _50_49 -> begin
true
end)) args))

# 37 "FStar.ToSMT.Encode.fst"
let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))

# 38 "FStar.ToSMT.Encode.fst"
let escape_null_name = (fun a -> if (a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = "_") then begin
(Prims.strcat a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText a.FStar_Absyn_Syntax.realname.FStar_Ident.idText)
end else begin
a.FStar_Absyn_Syntax.ppname.FStar_Ident.idText
end)

# 43 "FStar.ToSMT.Encode.fst"
let mk_typ_projector_name : FStar_Ident.lident  ->  FStar_Absyn_Syntax.btvdef  ->  Prims.string = (fun lid a -> (let _139_14 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (escape_null_name a))
in (FStar_All.pipe_left escape _139_14)))

# 45 "FStar.ToSMT.Encode.fst"
let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Absyn_Syntax.bvvdef  ->  Prims.string = (fun lid a -> (
# 46 "FStar.ToSMT.Encode.fst"
let a = (let _139_19 = (FStar_Absyn_Util.unmangle_field_name a.FStar_Absyn_Syntax.ppname)
in {FStar_Absyn_Syntax.ppname = _139_19; FStar_Absyn_Syntax.realname = a.FStar_Absyn_Syntax.realname})
in (let _139_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (escape_null_name a))
in (FStar_All.pipe_left escape _139_20))))

# 48 "FStar.ToSMT.Encode.fst"
let primitive_projector_by_pos : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (
# 49 "FStar.ToSMT.Encode.fst"
let fail = (fun _50_61 -> (match (()) with
| () -> begin
(let _139_30 = (let _139_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _139_29 lid.FStar_Ident.str))
in (FStar_All.failwith _139_30))
end))
in (
# 50 "FStar.ToSMT.Encode.fst"
let t = (FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _139_31 = (FStar_Absyn_Util.compress_typ t)
in _139_31.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _50_65) -> begin
if ((i < 0) || (i >= (FStar_List.length binders))) then begin
(fail ())
end else begin
(
# 55 "FStar.ToSMT.Encode.fst"
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

# 61 "FStar.ToSMT.Encode.fst"
let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _139_37 = (let _139_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _139_36))
in (FStar_All.pipe_left escape _139_37)))

# 62 "FStar.ToSMT.Encode.fst"
let mk_typ_projector : FStar_Ident.lident  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_ToSMT_Term.term = (fun lid a -> (let _139_43 = (let _139_42 = (mk_typ_projector_name lid a)
in (_139_42, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Type_sort))))
in (FStar_ToSMT_Term.mkFreeV _139_43)))

# 64 "FStar.ToSMT.Encode.fst"
let mk_term_projector : FStar_Ident.lident  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_ToSMT_Term.term = (fun lid a -> (let _139_49 = (let _139_48 = (mk_term_projector_name lid a)
in (_139_48, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _139_49)))

# 66 "FStar.ToSMT.Encode.fst"
let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_ToSMT_Term.term = (fun lid i -> (let _139_55 = (let _139_54 = (mk_term_projector_name_by_pos lid i)
in (_139_54, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _139_55)))

# 68 "FStar.ToSMT.Encode.fst"
let mk_data_tester = (fun env l x -> (FStar_ToSMT_Term.mk_tester (escape l.FStar_Ident.str) x))

# 71 "FStar.ToSMT.Encode.fst"
type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  FStar_Ident.ident  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_ToSMT_Term.term; next_id : Prims.unit  ->  Prims.int}

# 71 "FStar.ToSMT.Encode.fst"
let is_Mkvarops_t : varops_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkvarops_t"))))

# 83 "FStar.ToSMT.Encode.fst"
let varops : varops_t = (
# 84 "FStar.ToSMT.Encode.fst"
let initial_ctr = 10
in (
# 85 "FStar.ToSMT.Encode.fst"
let ctr = (FStar_Util.mk_ref initial_ctr)
in (
# 86 "FStar.ToSMT.Encode.fst"
let new_scope = (fun _50_100 -> (match (()) with
| () -> begin
(let _139_159 = (FStar_Util.smap_create 100)
in (let _139_158 = (FStar_Util.smap_create 100)
in (_139_159, _139_158)))
end))
in (
# 87 "FStar.ToSMT.Encode.fst"
let scopes = (let _139_161 = (let _139_160 = (new_scope ())
in (_139_160)::[])
in (FStar_Util.mk_ref _139_161))
in (
# 88 "FStar.ToSMT.Encode.fst"
let mk_unique = (fun y -> (
# 89 "FStar.ToSMT.Encode.fst"
let y = (escape y)
in (
# 90 "FStar.ToSMT.Encode.fst"
let y = (match ((let _139_165 = (FStar_ST.read scopes)
in (FStar_Util.find_map _139_165 (fun _50_108 -> (match (_50_108) with
| (names, _50_107) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_50_111) -> begin
(
# 92 "FStar.ToSMT.Encode.fst"
let _50_113 = (FStar_Util.incr ctr)
in (let _139_167 = (let _139_166 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _139_166))
in (Prims.strcat (Prims.strcat y "__") _139_167)))
end)
in (
# 93 "FStar.ToSMT.Encode.fst"
let top_scope = (let _139_169 = (let _139_168 = (FStar_ST.read scopes)
in (FStar_List.hd _139_168))
in (FStar_All.pipe_left Prims.fst _139_169))
in (
# 94 "FStar.ToSMT.Encode.fst"
let _50_117 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (
# 95 "FStar.ToSMT.Encode.fst"
let new_var = (fun pp rn -> (let _139_175 = (let _139_174 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _139_174 "__"))
in (Prims.strcat _139_175 rn.FStar_Ident.idText)))
in (
# 96 "FStar.ToSMT.Encode.fst"
let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (
# 97 "FStar.ToSMT.Encode.fst"
let next_id = (fun _50_125 -> (match (()) with
| () -> begin
(
# 97 "FStar.ToSMT.Encode.fst"
let _50_126 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (
# 98 "FStar.ToSMT.Encode.fst"
let fresh = (fun pfx -> (let _139_183 = (let _139_182 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _139_182))
in (FStar_Util.format2 "%s_%s" pfx _139_183)))
in (
# 99 "FStar.ToSMT.Encode.fst"
let string_const = (fun s -> (match ((let _139_187 = (FStar_ST.read scopes)
in (FStar_Util.find_map _139_187 (fun _50_135 -> (match (_50_135) with
| (_50_133, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))) with
| Some (f) -> begin
f
end
| None -> begin
(
# 102 "FStar.ToSMT.Encode.fst"
let id = (next_id ())
in (
# 103 "FStar.ToSMT.Encode.fst"
let f = (let _139_188 = (FStar_ToSMT_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxString _139_188))
in (
# 104 "FStar.ToSMT.Encode.fst"
let top_scope = (let _139_190 = (let _139_189 = (FStar_ST.read scopes)
in (FStar_List.hd _139_189))
in (FStar_All.pipe_left Prims.snd _139_190))
in (
# 105 "FStar.ToSMT.Encode.fst"
let _50_142 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (
# 107 "FStar.ToSMT.Encode.fst"
let push = (fun _50_145 -> (match (()) with
| () -> begin
(let _139_195 = (let _139_194 = (new_scope ())
in (let _139_193 = (FStar_ST.read scopes)
in (_139_194)::_139_193))
in (FStar_ST.op_Colon_Equals scopes _139_195))
end))
in (
# 108 "FStar.ToSMT.Encode.fst"
let pop = (fun _50_147 -> (match (()) with
| () -> begin
(let _139_199 = (let _139_198 = (FStar_ST.read scopes)
in (FStar_List.tl _139_198))
in (FStar_ST.op_Colon_Equals scopes _139_199))
end))
in (
# 109 "FStar.ToSMT.Encode.fst"
let mark = (fun _50_149 -> (match (()) with
| () -> begin
(push ())
end))
in (
# 110 "FStar.ToSMT.Encode.fst"
let reset_mark = (fun _50_151 -> (match (()) with
| () -> begin
(pop ())
end))
in (
# 111 "FStar.ToSMT.Encode.fst"
let commit_mark = (fun _50_153 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(
# 113 "FStar.ToSMT.Encode.fst"
let _50_166 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (
# 114 "FStar.ToSMT.Encode.fst"
let _50_171 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _50_174 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

# 128 "FStar.ToSMT.Encode.fst"
let unmangle = (fun x -> (let _139_215 = (let _139_214 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.ppname)
in (let _139_213 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.realname)
in (_139_214, _139_213)))
in (FStar_Absyn_Util.mkbvd _139_215)))

# 132 "FStar.ToSMT.Encode.fst"
type binding =
| Binding_var of (FStar_Absyn_Syntax.bvvdef * FStar_ToSMT_Term.term)
| Binding_tvar of (FStar_Absyn_Syntax.btvdef * FStar_ToSMT_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option)
| Binding_ftvar of (FStar_Ident.lident * Prims.string * FStar_ToSMT_Term.term Prims.option)

# 133 "FStar.ToSMT.Encode.fst"
let is_Binding_var = (fun _discr_ -> (match (_discr_) with
| Binding_var (_) -> begin
true
end
| _ -> begin
false
end))

# 134 "FStar.ToSMT.Encode.fst"
let is_Binding_tvar = (fun _discr_ -> (match (_discr_) with
| Binding_tvar (_) -> begin
true
end
| _ -> begin
false
end))

# 135 "FStar.ToSMT.Encode.fst"
let is_Binding_fvar = (fun _discr_ -> (match (_discr_) with
| Binding_fvar (_) -> begin
true
end
| _ -> begin
false
end))

# 136 "FStar.ToSMT.Encode.fst"
let is_Binding_ftvar = (fun _discr_ -> (match (_discr_) with
| Binding_ftvar (_) -> begin
true
end
| _ -> begin
false
end))

# 133 "FStar.ToSMT.Encode.fst"
let ___Binding_var____0 = (fun projectee -> (match (projectee) with
| Binding_var (_50_179) -> begin
_50_179
end))

# 134 "FStar.ToSMT.Encode.fst"
let ___Binding_tvar____0 = (fun projectee -> (match (projectee) with
| Binding_tvar (_50_182) -> begin
_50_182
end))

# 135 "FStar.ToSMT.Encode.fst"
let ___Binding_fvar____0 = (fun projectee -> (match (projectee) with
| Binding_fvar (_50_185) -> begin
_50_185
end))

# 136 "FStar.ToSMT.Encode.fst"
let ___Binding_ftvar____0 = (fun projectee -> (match (projectee) with
| Binding_ftvar (_50_188) -> begin
_50_188
end))

# 138 "FStar.ToSMT.Encode.fst"
let binder_of_eithervar = (fun v -> (v, None))

# 139 "FStar.ToSMT.Encode.fst"
type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_Tc_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_ToSMT_Term.sort Prims.list * FStar_ToSMT_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

# 139 "FStar.ToSMT.Encode.fst"
let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))

# 149 "FStar.ToSMT.Encode.fst"
let print_env : env_t  ->  Prims.string = (fun e -> (let _139_301 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _50_2 -> (match (_50_2) with
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
in (FStar_All.pipe_right _139_301 (FStar_String.concat ", "))))

# 156 "FStar.ToSMT.Encode.fst"
let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

# 158 "FStar.ToSMT.Encode.fst"
let caption_t : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string Prims.option = (fun env t -> if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _139_311 = (FStar_Absyn_Print.typ_to_string t)
in Some (_139_311))
end else begin
None
end)

# 163 "FStar.ToSMT.Encode.fst"
let fresh_fvar : Prims.string  ->  FStar_ToSMT_Term.sort  ->  (Prims.string * FStar_ToSMT_Term.term) = (fun x s -> (
# 163 "FStar.ToSMT.Encode.fst"
let xsym = (varops.fresh x)
in (let _139_316 = (FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _139_316))))

# 167 "FStar.ToSMT.Encode.fst"
let gen_term_var : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (
# 168 "FStar.ToSMT.Encode.fst"
let ysym = (let _139_321 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _139_321))
in (
# 169 "FStar.ToSMT.Encode.fst"
let y = (FStar_ToSMT_Term.mkFreeV (ysym, FStar_ToSMT_Term.Term_sort))
in (ysym, y, (
# 170 "FStar.ToSMT.Encode.fst"
let _50_232 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _50_232.tcenv; warn = _50_232.warn; cache = _50_232.cache; nolabels = _50_232.nolabels; use_zfuel_name = _50_232.use_zfuel_name; encode_non_total_function_typ = _50_232.encode_non_total_function_typ})))))

# 171 "FStar.ToSMT.Encode.fst"
let new_term_constant : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (
# 172 "FStar.ToSMT.Encode.fst"
let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (
# 173 "FStar.ToSMT.Encode.fst"
let y = (FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (
# 174 "FStar.ToSMT.Encode.fst"
let _50_238 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _50_238.depth; tcenv = _50_238.tcenv; warn = _50_238.warn; cache = _50_238.cache; nolabels = _50_238.nolabels; use_zfuel_name = _50_238.use_zfuel_name; encode_non_total_function_typ = _50_238.encode_non_total_function_typ})))))

# 175 "FStar.ToSMT.Encode.fst"
let push_term_var : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_ToSMT_Term.term  ->  env_t = (fun env x t -> (
# 176 "FStar.ToSMT.Encode.fst"
let _50_243 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _50_243.depth; tcenv = _50_243.tcenv; warn = _50_243.warn; cache = _50_243.cache; nolabels = _50_243.nolabels; use_zfuel_name = _50_243.use_zfuel_name; encode_non_total_function_typ = _50_243.encode_non_total_function_typ}))

# 177 "FStar.ToSMT.Encode.fst"
let lookup_term_var = (fun env a -> (match ((lookup_binding env (fun _50_3 -> (match (_50_3) with
| Binding_var (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _50_253 -> begin
None
end)))) with
| None -> begin
(let _139_336 = (let _139_335 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound term variable not found: %s" _139_335))
in (FStar_All.failwith _139_336))
end
| Some (b, t) -> begin
t
end))

# 183 "FStar.ToSMT.Encode.fst"
let gen_typ_var : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (
# 184 "FStar.ToSMT.Encode.fst"
let ysym = (let _139_341 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@a" _139_341))
in (
# 185 "FStar.ToSMT.Encode.fst"
let y = (FStar_ToSMT_Term.mkFreeV (ysym, FStar_ToSMT_Term.Type_sort))
in (ysym, y, (
# 186 "FStar.ToSMT.Encode.fst"
let _50_263 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _50_263.tcenv; warn = _50_263.warn; cache = _50_263.cache; nolabels = _50_263.nolabels; use_zfuel_name = _50_263.use_zfuel_name; encode_non_total_function_typ = _50_263.encode_non_total_function_typ})))))

# 187 "FStar.ToSMT.Encode.fst"
let new_typ_constant : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (
# 188 "FStar.ToSMT.Encode.fst"
let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (
# 189 "FStar.ToSMT.Encode.fst"
let y = (FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (
# 190 "FStar.ToSMT.Encode.fst"
let _50_269 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = _50_269.depth; tcenv = _50_269.tcenv; warn = _50_269.warn; cache = _50_269.cache; nolabels = _50_269.nolabels; use_zfuel_name = _50_269.use_zfuel_name; encode_non_total_function_typ = _50_269.encode_non_total_function_typ})))))

# 191 "FStar.ToSMT.Encode.fst"
let push_typ_var : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_ToSMT_Term.term  ->  env_t = (fun env x t -> (
# 192 "FStar.ToSMT.Encode.fst"
let _50_274 = env
in {bindings = (Binding_tvar ((x, t)))::env.bindings; depth = _50_274.depth; tcenv = _50_274.tcenv; warn = _50_274.warn; cache = _50_274.cache; nolabels = _50_274.nolabels; use_zfuel_name = _50_274.use_zfuel_name; encode_non_total_function_typ = _50_274.encode_non_total_function_typ}))

# 193 "FStar.ToSMT.Encode.fst"
let lookup_typ_var = (fun env a -> (match ((lookup_binding env (fun _50_4 -> (match (_50_4) with
| Binding_tvar (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _50_284 -> begin
None
end)))) with
| None -> begin
(let _139_356 = (let _139_355 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound type variable not found: %s" _139_355))
in (FStar_All.failwith _139_356))
end
| Some (b, t) -> begin
t
end))

# 199 "FStar.ToSMT.Encode.fst"
let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (
# 200 "FStar.ToSMT.Encode.fst"
let fname = (varops.new_fvar x)
in (
# 201 "FStar.ToSMT.Encode.fst"
let ftok = (Prims.strcat fname "@tok")
in (let _139_367 = (
# 202 "FStar.ToSMT.Encode.fst"
let _50_294 = env
in (let _139_366 = (let _139_365 = (let _139_364 = (let _139_363 = (let _139_362 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _139_361 -> Some (_139_361)) _139_362))
in (x, fname, _139_363, None))
in Binding_fvar (_139_364))
in (_139_365)::env.bindings)
in {bindings = _139_366; depth = _50_294.depth; tcenv = _50_294.tcenv; warn = _50_294.warn; cache = _50_294.cache; nolabels = _50_294.nolabels; use_zfuel_name = _50_294.use_zfuel_name; encode_non_total_function_typ = _50_294.encode_non_total_function_typ}))
in (fname, ftok, _139_367)))))

# 203 "FStar.ToSMT.Encode.fst"
let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _50_5 -> (match (_50_5) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _50_306 -> begin
None
end))))

# 205 "FStar.ToSMT.Encode.fst"
let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _139_378 = (let _139_377 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Name not found: %s" _139_377))
in (FStar_All.failwith _139_378))
end
| Some (s) -> begin
s
end))

# 209 "FStar.ToSMT.Encode.fst"
let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (
# 210 "FStar.ToSMT.Encode.fst"
let _50_316 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _50_316.depth; tcenv = _50_316.tcenv; warn = _50_316.warn; cache = _50_316.cache; nolabels = _50_316.nolabels; use_zfuel_name = _50_316.use_zfuel_name; encode_non_total_function_typ = _50_316.encode_non_total_function_typ}))

# 211 "FStar.ToSMT.Encode.fst"
let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (
# 212 "FStar.ToSMT.Encode.fst"
let _50_325 = (lookup_lid env x)
in (match (_50_325) with
| (t1, t2, _50_324) -> begin
(
# 213 "FStar.ToSMT.Encode.fst"
let t3 = (let _139_395 = (let _139_394 = (let _139_393 = (FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_139_393)::[])
in (f, _139_394))
in (FStar_ToSMT_Term.mkApp _139_395))
in (
# 214 "FStar.ToSMT.Encode.fst"
let _50_327 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _50_327.depth; tcenv = _50_327.tcenv; warn = _50_327.warn; cache = _50_327.cache; nolabels = _50_327.nolabels; use_zfuel_name = _50_327.use_zfuel_name; encode_non_total_function_typ = _50_327.encode_non_total_function_typ}))
end)))

# 215 "FStar.ToSMT.Encode.fst"
let lookup_free_var = (fun env a -> (
# 216 "FStar.ToSMT.Encode.fst"
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
| FStar_ToSMT_Term.App (_50_342, fuel::[]) -> begin
if (let _139_399 = (let _139_398 = (FStar_ToSMT_Term.fv_of_term fuel)
in (FStar_All.pipe_right _139_398 Prims.fst))
in (FStar_Util.starts_with _139_399 "fuel")) then begin
(let _139_400 = (FStar_ToSMT_Term.mkFreeV (name, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_ApplyEF _139_400 fuel))
end else begin
t
end
end
| _50_348 -> begin
t
end)
end
| _50_350 -> begin
(let _139_402 = (let _139_401 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _139_401))
in (FStar_All.failwith _139_402))
end)
end)
end)))

# 230 "FStar.ToSMT.Encode.fst"
let lookup_free_var_name = (fun env a -> (
# 230 "FStar.ToSMT.Encode.fst"
let _50_358 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_50_358) with
| (x, _50_355, _50_357) -> begin
x
end)))

# 231 "FStar.ToSMT.Encode.fst"
let lookup_free_var_sym = (fun env a -> (
# 232 "FStar.ToSMT.Encode.fst"
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
| FStar_ToSMT_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _50_386 -> begin
(FStar_ToSMT_Term.Var (name), [])
end)
end)
end)
end)))

# 244 "FStar.ToSMT.Encode.fst"
let new_typ_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (
# 245 "FStar.ToSMT.Encode.fst"
let fname = (varops.new_fvar x)
in (
# 246 "FStar.ToSMT.Encode.fst"
let ftok = (Prims.strcat fname "@tok")
in (let _139_417 = (
# 247 "FStar.ToSMT.Encode.fst"
let _50_391 = env
in (let _139_416 = (let _139_415 = (let _139_414 = (let _139_413 = (let _139_412 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _139_411 -> Some (_139_411)) _139_412))
in (x, fname, _139_413))
in Binding_ftvar (_139_414))
in (_139_415)::env.bindings)
in {bindings = _139_416; depth = _50_391.depth; tcenv = _50_391.tcenv; warn = _50_391.warn; cache = _50_391.cache; nolabels = _50_391.nolabels; use_zfuel_name = _50_391.use_zfuel_name; encode_non_total_function_typ = _50_391.encode_non_total_function_typ}))
in (fname, ftok, _139_417)))))

# 248 "FStar.ToSMT.Encode.fst"
let lookup_tlid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option) = (fun env a -> (match ((lookup_binding env (fun _50_6 -> (match (_50_6) with
| Binding_ftvar (b, t1, t2) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2))
end
| _50_402 -> begin
None
end)))) with
| None -> begin
(let _139_424 = (let _139_423 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Type name not found: %s" _139_423))
in (FStar_All.failwith _139_424))
end
| Some (s) -> begin
s
end))

# 252 "FStar.ToSMT.Encode.fst"
let push_free_tvar : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (
# 253 "FStar.ToSMT.Encode.fst"
let _50_410 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _50_410.depth; tcenv = _50_410.tcenv; warn = _50_410.warn; cache = _50_410.cache; nolabels = _50_410.nolabels; use_zfuel_name = _50_410.use_zfuel_name; encode_non_total_function_typ = _50_410.encode_non_total_function_typ}))

# 254 "FStar.ToSMT.Encode.fst"
let lookup_free_tvar = (fun env a -> (match ((let _139_435 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _139_435 Prims.snd))) with
| None -> begin
(let _139_437 = (let _139_436 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Type name not found: %s" _139_436))
in (FStar_All.failwith _139_437))
end
| Some (t) -> begin
t
end))

# 258 "FStar.ToSMT.Encode.fst"
let lookup_free_tvar_name = (fun env a -> (let _139_440 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _139_440 Prims.fst)))

# 260 "FStar.ToSMT.Encode.fst"
let tok_of_name : env_t  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _50_7 -> (match (_50_7) with
| (Binding_fvar (_, nm', tok, _)) | (Binding_ftvar (_, nm', tok)) when (nm = nm') -> begin
tok
end
| _50_435 -> begin
None
end))))

# 270 "FStar.ToSMT.Encode.fst"
let mkForall_fuel' = (fun n _50_440 -> (match (_50_440) with
| (pats, vars, body) -> begin
(
# 271 "FStar.ToSMT.Encode.fst"
let fallback = (fun _50_442 -> (match (()) with
| () -> begin
(FStar_ToSMT_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(
# 274 "FStar.ToSMT.Encode.fst"
let _50_445 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_50_445) with
| (fsym, fterm) -> begin
(
# 275 "FStar.ToSMT.Encode.fst"
let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var ("HasType"), args) -> begin
(FStar_ToSMT_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _50_455 -> begin
p
end)))))
in (
# 279 "FStar.ToSMT.Encode.fst"
let pats = (FStar_List.map add_fuel pats)
in (
# 280 "FStar.ToSMT.Encode.fst"
let body = (match (body.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, guard::body'::[]) -> begin
(
# 282 "FStar.ToSMT.Encode.fst"
let guard = (match (guard.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.And, guards) -> begin
(let _139_453 = (add_fuel guards)
in (FStar_ToSMT_Term.mk_and_l _139_453))
end
| _50_468 -> begin
(let _139_454 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _139_454 FStar_List.hd))
end)
in (FStar_ToSMT_Term.mkImp (guard, body')))
end
| _50_471 -> begin
body
end)
in (
# 287 "FStar.ToSMT.Encode.fst"
let vars = ((fsym, FStar_ToSMT_Term.Fuel_sort))::vars
in (FStar_ToSMT_Term.mkForall (pats, vars, body))))))
end))
end)
end))

# 290 "FStar.ToSMT.Encode.fst"
let mkForall_fuel : (FStar_ToSMT_Term.pat Prims.list Prims.list * FStar_ToSMT_Term.fvs * FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term = (mkForall_fuel' 1)

# 292 "FStar.ToSMT.Encode.fst"
let head_normal : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.bool = (fun env t -> (
# 293 "FStar.ToSMT.Encode.fst"
let t = (FStar_Absyn_Util.unmeta_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Typ_fun (_)) | (FStar_Absyn_Syntax.Typ_refine (_)) | (FStar_Absyn_Syntax.Typ_btvar (_)) | (FStar_Absyn_Syntax.Typ_uvar (_)) | (FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| (FStar_Absyn_Syntax.Typ_const (v)) | (FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (v); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(let _139_460 = (FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _139_460 FStar_Option.isNone))
end
| _50_509 -> begin
false
end)))

# 304 "FStar.ToSMT.Encode.fst"
let whnf : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t -> if (head_normal env t) then begin
t
end else begin
(FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.WHNF)::(FStar_Tc_Normalize.DeltaHard)::[]) env.tcenv t)
end)

# 307 "FStar.ToSMT.Encode.fst"
let whnf_e : env_t  ->  FStar_Absyn_Syntax.exp  ->  FStar_Absyn_Syntax.exp = (fun env e -> (FStar_Tc_Normalize.norm_exp ((FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.WHNF)::[]) env.tcenv e))

# 308 "FStar.ToSMT.Encode.fst"
let norm_t : env_t  ->  FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun env t -> (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.Beta)::[]) env.tcenv t))

# 309 "FStar.ToSMT.Encode.fst"
let norm_k : env_t  ->  FStar_Absyn_Syntax.knd  ->  FStar_Absyn_Syntax.knd = (fun env k -> (FStar_Tc_Normalize.normalize_kind env.tcenv k))

# 310 "FStar.ToSMT.Encode.fst"
let trivial_post : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun t -> (let _139_482 = (let _139_481 = (let _139_479 = (FStar_Absyn_Syntax.null_v_binder t)
in (_139_479)::[])
in (let _139_480 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (_139_481, _139_480)))
in (FStar_Absyn_Syntax.mk_Typ_lam _139_482 None t.FStar_Absyn_Syntax.pos)))

# 313 "FStar.ToSMT.Encode.fst"
let mk_ApplyE : FStar_ToSMT_Term.term  ->  (Prims.string * FStar_ToSMT_Term.sort) Prims.list  ->  FStar_ToSMT_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _139_489 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyET out _139_489))
end
| FStar_ToSMT_Term.Fuel_sort -> begin
(let _139_490 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEF out _139_490))
end
| _50_526 -> begin
(let _139_491 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEE out _139_491))
end)) e)))

# 318 "FStar.ToSMT.Encode.fst"
let mk_ApplyE_args : FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list  ->  FStar_ToSMT_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out arg -> (match (arg) with
| FStar_Util.Inl (t) -> begin
(FStar_ToSMT_Term.mk_ApplyET out t)
end
| FStar_Util.Inr (e) -> begin
(FStar_ToSMT_Term.mk_ApplyEE out e)
end)) e)))

# 323 "FStar.ToSMT.Encode.fst"
let mk_ApplyT : FStar_ToSMT_Term.term  ->  (Prims.string * FStar_ToSMT_Term.sort) Prims.list  ->  FStar_ToSMT_Term.term = (fun t vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _139_504 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTT out _139_504))
end
| _50_541 -> begin
(let _139_505 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTE out _139_505))
end)) t)))

# 327 "FStar.ToSMT.Encode.fst"
let mk_ApplyT_args : FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list  ->  FStar_ToSMT_Term.term = (fun t args -> (FStar_All.pipe_right args (FStar_List.fold_left (fun out arg -> (match (arg) with
| FStar_Util.Inl (t) -> begin
(FStar_ToSMT_Term.mk_ApplyTT out t)
end
| FStar_Util.Inr (e) -> begin
(FStar_ToSMT_Term.mk_ApplyTE out e)
end)) t)))

# 331 "FStar.ToSMT.Encode.fst"
let is_app : FStar_ToSMT_Term.op  ->  Prims.bool = (fun _50_8 -> (match (_50_8) with
| (FStar_ToSMT_Term.Var ("ApplyTT")) | (FStar_ToSMT_Term.Var ("ApplyTE")) | (FStar_ToSMT_Term.Var ("ApplyET")) | (FStar_ToSMT_Term.Var ("ApplyEE")) -> begin
true
end
| _50_560 -> begin
false
end))

# 338 "FStar.ToSMT.Encode.fst"
let is_eta : env_t  ->  FStar_ToSMT_Term.fv Prims.list  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term Prims.option = (fun env vars t -> (
# 339 "FStar.ToSMT.Encode.fst"
let rec aux = (fun t xs -> (match ((t.FStar_ToSMT_Term.tm, xs)) with
| (FStar_ToSMT_Term.App (app, f::{FStar_ToSMT_Term.tm = FStar_ToSMT_Term.FreeV (y); FStar_ToSMT_Term.hash = _50_571; FStar_ToSMT_Term.freevars = _50_569}::[]), x::xs) when ((is_app app) && (FStar_ToSMT_Term.fv_eq x y)) -> begin
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
# 350 "FStar.ToSMT.Encode.fst"
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

# 383 "FStar.ToSMT.Encode.fst"
type label =
(FStar_ToSMT_Term.fv * Prims.string * FStar_Range.range)

# 384 "FStar.ToSMT.Encode.fst"
type labels =
label Prims.list

# 385 "FStar.ToSMT.Encode.fst"
type pattern =
{pat_vars : (FStar_Absyn_Syntax.either_var * FStar_ToSMT_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t); guard : FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term; projections : FStar_ToSMT_Term.term  ->  (FStar_Absyn_Syntax.either_var * FStar_ToSMT_Term.term) Prims.list}

# 385 "FStar.ToSMT.Encode.fst"
let is_Mkpattern : pattern  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkpattern"))))

# 391 "FStar.ToSMT.Encode.fst"
exception Let_rec_unencodeable

# 391 "FStar.ToSMT.Encode.fst"
let is_Let_rec_unencodeable = (fun _discr_ -> (match (_discr_) with
| Let_rec_unencodeable (_) -> begin
true
end
| _ -> begin
false
end))

# 393 "FStar.ToSMT.Encode.fst"
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
(let _139_564 = (let _139_563 = (let _139_562 = (let _139_561 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_ToSMT_Term.boxInt _139_561))
in (_139_562)::[])
in ("FStar.Char.char", _139_563))
in (FStar_ToSMT_Term.mkApp _139_564))
end
| FStar_Const.Const_int (i, None) -> begin
(let _139_565 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _139_565))
end
| FStar_Const.Const_int (i, Some (q)) -> begin
(let _139_569 = (let _139_568 = (let _139_567 = (let _139_566 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _139_566))
in (_139_567)::[])
in ((FStar_Const.string_of_int_qualifier q), _139_568))
in (FStar_ToSMT_Term.mkApp _139_569))
end
| FStar_Const.Const_string (bytes, _50_629) -> begin
(let _139_570 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _139_570))
end
| c -> begin
(let _139_572 = (let _139_571 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s\n" _139_571))
in (FStar_All.failwith _139_572))
end))

# 403 "FStar.ToSMT.Encode.fst"
let as_function_typ : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t0 -> (
# 404 "FStar.ToSMT.Encode.fst"
let rec aux = (fun norm t -> (
# 405 "FStar.ToSMT.Encode.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_50_640) -> begin
t
end
| FStar_Absyn_Syntax.Typ_refine (_50_643) -> begin
(let _139_581 = (FStar_Absyn_Util.unrefine t)
in (aux true _139_581))
end
| _50_646 -> begin
if norm then begin
(let _139_582 = (whnf env t)
in (aux false _139_582))
end else begin
(let _139_585 = (let _139_584 = (FStar_Range.string_of_range t0.FStar_Absyn_Syntax.pos)
in (let _139_583 = (FStar_Absyn_Print.typ_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _139_584 _139_583)))
in (FStar_All.failwith _139_585))
end
end)))
in (aux true t0)))

# 414 "FStar.ToSMT.Encode.fst"
let rec encode_knd_term : FStar_Absyn_Syntax.knd  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun k env -> (match ((let _139_622 = (FStar_Absyn_Util.compress_kind k)
in _139_622.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
(FStar_ToSMT_Term.mk_Kind_type, [])
end
| FStar_Absyn_Syntax.Kind_abbrev (_50_651, k0) -> begin
(
# 419 "FStar.ToSMT.Encode.fst"
let _50_655 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _139_624 = (FStar_Absyn_Print.kind_to_string k)
in (let _139_623 = (FStar_Absyn_Print.kind_to_string k0)
in (FStar_Util.print2 "Encoding kind abbrev %s, expanded to %s\n" _139_624 _139_623)))
end else begin
()
end
in (encode_knd_term k0 env))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, _50_659) -> begin
(let _139_626 = (let _139_625 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Kind_uvar _139_625))
in (_139_626, []))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, kbody) -> begin
(
# 427 "FStar.ToSMT.Encode.fst"
let tsym = (let _139_627 = (varops.fresh "t")
in (_139_627, FStar_ToSMT_Term.Type_sort))
in (
# 428 "FStar.ToSMT.Encode.fst"
let t = (FStar_ToSMT_Term.mkFreeV tsym)
in (
# 429 "FStar.ToSMT.Encode.fst"
let _50_674 = (encode_binders None bs env)
in (match (_50_674) with
| (vars, guards, env', decls, _50_673) -> begin
(
# 430 "FStar.ToSMT.Encode.fst"
let app = (mk_ApplyT t vars)
in (
# 431 "FStar.ToSMT.Encode.fst"
let _50_678 = (encode_knd kbody env' app)
in (match (_50_678) with
| (kbody, decls') -> begin
(
# 433 "FStar.ToSMT.Encode.fst"
let rec aux = (fun app vars guards -> (match ((vars, guards)) with
| ([], []) -> begin
kbody
end
| (x::vars, g::guards) -> begin
(
# 436 "FStar.ToSMT.Encode.fst"
let app = (mk_ApplyT app ((x)::[]))
in (
# 437 "FStar.ToSMT.Encode.fst"
let body = (aux app vars guards)
in (
# 438 "FStar.ToSMT.Encode.fst"
let body = (match (vars) with
| [] -> begin
body
end
| _50_697 -> begin
(let _139_636 = (let _139_635 = (let _139_634 = (FStar_ToSMT_Term.mk_PreKind app)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _139_634))
in (_139_635, body))
in (FStar_ToSMT_Term.mkAnd _139_636))
end)
in (let _139_638 = (let _139_637 = (FStar_ToSMT_Term.mkImp (g, body))
in (((app)::[])::[], (x)::[], _139_637))
in (FStar_ToSMT_Term.mkForall _139_638)))))
end
| _50_700 -> begin
(FStar_All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (
# 444 "FStar.ToSMT.Encode.fst"
let k_interp = (aux t vars guards)
in (
# 445 "FStar.ToSMT.Encode.fst"
let cvars = (let _139_640 = (FStar_ToSMT_Term.free_variables k_interp)
in (FStar_All.pipe_right _139_640 (FStar_List.filter (fun _50_705 -> (match (_50_705) with
| (x, _50_704) -> begin
(x <> (Prims.fst tsym))
end)))))
in (
# 446 "FStar.ToSMT.Encode.fst"
let tkey = (FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (k', sorts, _50_711) -> begin
(let _139_643 = (let _139_642 = (let _139_641 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (k', _139_641))
in (FStar_ToSMT_Term.mkApp _139_642))
in (_139_643, []))
end
| None -> begin
(
# 452 "FStar.ToSMT.Encode.fst"
let ksym = (varops.fresh "Kind_arrow")
in (
# 453 "FStar.ToSMT.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 454 "FStar.ToSMT.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _139_644 = (FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_139_644))
end else begin
None
end
in (
# 460 "FStar.ToSMT.Encode.fst"
let kdecl = FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, FStar_ToSMT_Term.Kind_sort, caption))
in (
# 462 "FStar.ToSMT.Encode.fst"
let k = (let _139_646 = (let _139_645 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _139_645))
in (FStar_ToSMT_Term.mkApp _139_646))
in (
# 463 "FStar.ToSMT.Encode.fst"
let t_has_k = (FStar_ToSMT_Term.mk_HasKind t k)
in (
# 464 "FStar.ToSMT.Encode.fst"
let k_interp = (let _139_655 = (let _139_654 = (let _139_653 = (let _139_652 = (let _139_651 = (let _139_650 = (let _139_649 = (let _139_648 = (let _139_647 = (FStar_ToSMT_Term.mk_PreKind t)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _139_647))
in (_139_648, k_interp))
in (FStar_ToSMT_Term.mkAnd _139_649))
in (t_has_k, _139_650))
in (FStar_ToSMT_Term.mkIff _139_651))
in (((t_has_k)::[])::[], (tsym)::cvars, _139_652))
in (FStar_ToSMT_Term.mkForall _139_653))
in (_139_654, Some ((Prims.strcat ksym " interpretation"))))
in FStar_ToSMT_Term.Assume (_139_655))
in (
# 470 "FStar.ToSMT.Encode.fst"
let k_decls = (FStar_List.append (FStar_List.append decls decls') ((kdecl)::(k_interp)::[]))
in (
# 471 "FStar.ToSMT.Encode.fst"
let _50_723 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _50_726 -> begin
(let _139_657 = (let _139_656 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.format1 "Unknown kind: %s" _139_656))
in (FStar_All.failwith _139_657))
end))
and encode_knd : FStar_Absyn_Syntax.knd  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decl Prims.list) = (fun k env t -> (
# 479 "FStar.ToSMT.Encode.fst"
let _50_732 = (encode_knd_term k env)
in (match (_50_732) with
| (k, decls) -> begin
(let _139_661 = (FStar_ToSMT_Term.mk_HasKind t k)
in (_139_661, decls))
end)))
and encode_binders : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.binders  ->  env_t  ->  (FStar_ToSMT_Term.fv Prims.list * FStar_ToSMT_Term.term Prims.list * env_t * FStar_ToSMT_Term.decls_t * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list) = (fun fuel_opt bs env -> (
# 489 "FStar.ToSMT.Encode.fst"
let _50_736 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _139_665 = (FStar_Absyn_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _139_665))
end else begin
()
end
in (
# 491 "FStar.ToSMT.Encode.fst"
let _50_786 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _50_743 b -> (match (_50_743) with
| (vars, guards, env, decls, names) -> begin
(
# 492 "FStar.ToSMT.Encode.fst"
let _50_780 = (match ((Prims.fst b)) with
| FStar_Util.Inl ({FStar_Absyn_Syntax.v = a; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _50_746}) -> begin
(
# 494 "FStar.ToSMT.Encode.fst"
let a = (unmangle a)
in (
# 495 "FStar.ToSMT.Encode.fst"
let _50_755 = (gen_typ_var env a)
in (match (_50_755) with
| (aasym, aa, env') -> begin
(
# 496 "FStar.ToSMT.Encode.fst"
let _50_756 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _139_669 = (FStar_Absyn_Print.strBvd a)
in (let _139_668 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.print3 "Encoding type binder %s (%s) at kind %s\n" _139_669 aasym _139_668)))
end else begin
()
end
in (
# 498 "FStar.ToSMT.Encode.fst"
let _50_760 = (encode_knd k env aa)
in (match (_50_760) with
| (guard_a_k, decls') -> begin
((aasym, FStar_ToSMT_Term.Type_sort), guard_a_k, env', decls', FStar_Util.Inl (a))
end)))
end)))
end
| FStar_Util.Inr ({FStar_Absyn_Syntax.v = x; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _50_762}) -> begin
(
# 506 "FStar.ToSMT.Encode.fst"
let x = (unmangle x)
in (
# 507 "FStar.ToSMT.Encode.fst"
let _50_771 = (gen_term_var env x)
in (match (_50_771) with
| (xxsym, xx, env') -> begin
(
# 508 "FStar.ToSMT.Encode.fst"
let _50_774 = (let _139_670 = (norm_t env t)
in (encode_typ_pred fuel_opt _139_670 env xx))
in (match (_50_774) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_ToSMT_Term.Term_sort), guard_x_t, env', decls', FStar_Util.Inr (x))
end))
end)))
end)
in (match (_50_780) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_50_786) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_typ_pred : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun fuel_opt t env e -> (
# 523 "FStar.ToSMT.Encode.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (
# 524 "FStar.ToSMT.Encode.fst"
let _50_794 = (encode_typ_term t env)
in (match (_50_794) with
| (t, decls) -> begin
(let _139_675 = (FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_139_675, decls))
end))))
and encode_typ_pred' : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun fuel_opt t env e -> (
# 528 "FStar.ToSMT.Encode.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (
# 529 "FStar.ToSMT.Encode.fst"
let _50_802 = (encode_typ_term t env)
in (match (_50_802) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _139_680 = (FStar_ToSMT_Term.mk_HasTypeZ e t)
in (_139_680, decls))
end
| Some (f) -> begin
(let _139_681 = (FStar_ToSMT_Term.mk_HasTypeFuel f e t)
in (_139_681, decls))
end)
end))))
and encode_typ_term : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun t env -> (
# 536 "FStar.ToSMT.Encode.fst"
let t0 = (FStar_Absyn_Util.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _139_684 = (lookup_typ_var env a)
in (_139_684, []))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _139_685 = (lookup_free_tvar env fv)
in (_139_685, []))
end
| FStar_Absyn_Syntax.Typ_fun (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (FStar_Absyn_Util.is_tot_or_gtot_comp res)) then begin
(
# 549 "FStar.ToSMT.Encode.fst"
let _50_823 = (encode_binders None binders env)
in (match (_50_823) with
| (vars, guards, env', decls, _50_822) -> begin
(
# 550 "FStar.ToSMT.Encode.fst"
let fsym = (let _139_686 = (varops.fresh "f")
in (_139_686, FStar_ToSMT_Term.Term_sort))
in (
# 551 "FStar.ToSMT.Encode.fst"
let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (
# 552 "FStar.ToSMT.Encode.fst"
let app = (mk_ApplyE f vars)
in (
# 553 "FStar.ToSMT.Encode.fst"
let _50_829 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_50_829) with
| (pre_opt, res_t) -> begin
(
# 554 "FStar.ToSMT.Encode.fst"
let _50_832 = (encode_typ_pred None res_t env' app)
in (match (_50_832) with
| (res_pred, decls') -> begin
(
# 555 "FStar.ToSMT.Encode.fst"
let _50_841 = (match (pre_opt) with
| None -> begin
(let _139_687 = (FStar_ToSMT_Term.mk_and_l guards)
in (_139_687, decls))
end
| Some (pre) -> begin
(
# 558 "FStar.ToSMT.Encode.fst"
let _50_838 = (encode_formula pre env')
in (match (_50_838) with
| (guard, decls0) -> begin
(let _139_688 = (FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_139_688, (FStar_List.append decls decls0)))
end))
end)
in (match (_50_841) with
| (guards, guard_decls) -> begin
(
# 560 "FStar.ToSMT.Encode.fst"
let t_interp = (let _139_690 = (let _139_689 = (FStar_ToSMT_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _139_689))
in (FStar_ToSMT_Term.mkForall _139_690))
in (
# 565 "FStar.ToSMT.Encode.fst"
let cvars = (let _139_692 = (FStar_ToSMT_Term.free_variables t_interp)
in (FStar_All.pipe_right _139_692 (FStar_List.filter (fun _50_846 -> (match (_50_846) with
| (x, _50_845) -> begin
(x <> (Prims.fst fsym))
end)))))
in (
# 566 "FStar.ToSMT.Encode.fst"
let tkey = (FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t', sorts, _50_852) -> begin
(let _139_695 = (let _139_694 = (let _139_693 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t', _139_693))
in (FStar_ToSMT_Term.mkApp _139_694))
in (_139_695, []))
end
| None -> begin
(
# 572 "FStar.ToSMT.Encode.fst"
let tsym = (varops.fresh "Typ_fun")
in (
# 573 "FStar.ToSMT.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 574 "FStar.ToSMT.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _139_696 = (FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_139_696))
end else begin
None
end
in (
# 579 "FStar.ToSMT.Encode.fst"
let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, caption))
in (
# 581 "FStar.ToSMT.Encode.fst"
let t = (let _139_698 = (let _139_697 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _139_697))
in (FStar_ToSMT_Term.mkApp _139_698))
in (
# 582 "FStar.ToSMT.Encode.fst"
let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (
# 584 "FStar.ToSMT.Encode.fst"
let k_assumption = (let _139_700 = (let _139_699 = (FStar_ToSMT_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_139_699, Some ((Prims.strcat tsym " kinding"))))
in FStar_ToSMT_Term.Assume (_139_700))
in (
# 586 "FStar.ToSMT.Encode.fst"
let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (
# 587 "FStar.ToSMT.Encode.fst"
let f_has_t_z = (FStar_ToSMT_Term.mk_HasTypeZ f t)
in (
# 588 "FStar.ToSMT.Encode.fst"
let pre_typing = (let _139_707 = (let _139_706 = (let _139_705 = (let _139_704 = (let _139_703 = (let _139_702 = (let _139_701 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _139_701))
in (f_has_t, _139_702))
in (FStar_ToSMT_Term.mkImp _139_703))
in (((f_has_t)::[])::[], (fsym)::cvars, _139_704))
in (mkForall_fuel _139_705))
in (_139_706, Some ("pre-typing for functions")))
in FStar_ToSMT_Term.Assume (_139_707))
in (
# 589 "FStar.ToSMT.Encode.fst"
let t_interp = (let _139_711 = (let _139_710 = (let _139_709 = (let _139_708 = (FStar_ToSMT_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _139_708))
in (FStar_ToSMT_Term.mkForall _139_709))
in (_139_710, Some ((Prims.strcat tsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_139_711))
in (
# 592 "FStar.ToSMT.Encode.fst"
let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (
# 593 "FStar.ToSMT.Encode.fst"
let _50_868 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(
# 597 "FStar.ToSMT.Encode.fst"
let tsym = (varops.fresh "Non_total_Typ_fun")
in (
# 598 "FStar.ToSMT.Encode.fst"
let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, [], FStar_ToSMT_Term.Type_sort, None))
in (
# 599 "FStar.ToSMT.Encode.fst"
let t = (FStar_ToSMT_Term.mkApp (tsym, []))
in (
# 600 "FStar.ToSMT.Encode.fst"
let t_kinding = (let _139_713 = (let _139_712 = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (_139_712, None))
in FStar_ToSMT_Term.Assume (_139_713))
in (
# 601 "FStar.ToSMT.Encode.fst"
let fsym = ("f", FStar_ToSMT_Term.Term_sort)
in (
# 602 "FStar.ToSMT.Encode.fst"
let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (
# 603 "FStar.ToSMT.Encode.fst"
let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (
# 604 "FStar.ToSMT.Encode.fst"
let t_interp = (let _139_720 = (let _139_719 = (let _139_718 = (let _139_717 = (let _139_716 = (let _139_715 = (let _139_714 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _139_714))
in (f_has_t, _139_715))
in (FStar_ToSMT_Term.mkImp _139_716))
in (((f_has_t)::[])::[], (fsym)::[], _139_717))
in (mkForall_fuel _139_718))
in (_139_719, Some ("pre-typing")))
in FStar_ToSMT_Term.Assume (_139_720))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end
| FStar_Absyn_Syntax.Typ_refine (_50_879) -> begin
(
# 611 "FStar.ToSMT.Encode.fst"
let _50_898 = (match ((FStar_Tc_Normalize.normalize_refinement [] env.tcenv t0)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_refine (x, f); FStar_Absyn_Syntax.tk = _50_888; FStar_Absyn_Syntax.pos = _50_886; FStar_Absyn_Syntax.fvs = _50_884; FStar_Absyn_Syntax.uvs = _50_882} -> begin
(x, f)
end
| _50_895 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_50_898) with
| (x, f) -> begin
(
# 615 "FStar.ToSMT.Encode.fst"
let _50_901 = (encode_typ_term x.FStar_Absyn_Syntax.sort env)
in (match (_50_901) with
| (base_t, decls) -> begin
(
# 616 "FStar.ToSMT.Encode.fst"
let _50_905 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_50_905) with
| (x, xtm, env') -> begin
(
# 617 "FStar.ToSMT.Encode.fst"
let _50_908 = (encode_formula f env')
in (match (_50_908) with
| (refinement, decls') -> begin
(
# 619 "FStar.ToSMT.Encode.fst"
let _50_911 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_50_911) with
| (fsym, fterm) -> begin
(
# 621 "FStar.ToSMT.Encode.fst"
let encoding = (let _139_722 = (let _139_721 = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_139_721, refinement))
in (FStar_ToSMT_Term.mkAnd _139_722))
in (
# 623 "FStar.ToSMT.Encode.fst"
let cvars = (let _139_724 = (FStar_ToSMT_Term.free_variables encoding)
in (FStar_All.pipe_right _139_724 (FStar_List.filter (fun _50_916 -> (match (_50_916) with
| (y, _50_915) -> begin
((y <> x) && (y <> fsym))
end)))))
in (
# 624 "FStar.ToSMT.Encode.fst"
let xfv = (x, FStar_ToSMT_Term.Term_sort)
in (
# 625 "FStar.ToSMT.Encode.fst"
let ffv = (fsym, FStar_ToSMT_Term.Fuel_sort)
in (
# 626 "FStar.ToSMT.Encode.fst"
let tkey = (FStar_ToSMT_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _50_923, _50_925) -> begin
(let _139_727 = (let _139_726 = (let _139_725 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t, _139_725))
in (FStar_ToSMT_Term.mkApp _139_726))
in (_139_727, []))
end
| None -> begin
(
# 633 "FStar.ToSMT.Encode.fst"
let tsym = (varops.fresh "Typ_refine")
in (
# 634 "FStar.ToSMT.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 635 "FStar.ToSMT.Encode.fst"
let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, None))
in (
# 636 "FStar.ToSMT.Encode.fst"
let t = (let _139_729 = (let _139_728 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _139_728))
in (FStar_ToSMT_Term.mkApp _139_729))
in (
# 638 "FStar.ToSMT.Encode.fst"
let x_has_t = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (
# 639 "FStar.ToSMT.Encode.fst"
let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (
# 641 "FStar.ToSMT.Encode.fst"
let t_kinding = (FStar_ToSMT_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (
# 642 "FStar.ToSMT.Encode.fst"
let assumption = (let _139_731 = (let _139_730 = (FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _139_730))
in (FStar_ToSMT_Term.mkForall _139_731))
in (
# 644 "FStar.ToSMT.Encode.fst"
let t_decls = (let _139_738 = (let _139_737 = (let _139_736 = (let _139_735 = (let _139_734 = (let _139_733 = (let _139_732 = (FStar_Absyn_Print.typ_to_string t0)
in Some (_139_732))
in (assumption, _139_733))
in FStar_ToSMT_Term.Assume (_139_734))
in (_139_735)::[])
in (FStar_ToSMT_Term.Assume ((t_kinding, None)))::_139_736)
in (tdecl)::_139_737)
in (FStar_List.append (FStar_List.append decls decls') _139_738))
in (
# 649 "FStar.ToSMT.Encode.fst"
let _50_938 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
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
# 654 "FStar.ToSMT.Encode.fst"
let ttm = (let _139_739 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _139_739))
in (
# 655 "FStar.ToSMT.Encode.fst"
let _50_947 = (encode_knd k env ttm)
in (match (_50_947) with
| (t_has_k, decls) -> begin
(
# 656 "FStar.ToSMT.Encode.fst"
let d = FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(
# 660 "FStar.ToSMT.Encode.fst"
let is_full_app = (fun _50_954 -> (match (()) with
| () -> begin
(
# 661 "FStar.ToSMT.Encode.fst"
let kk = (FStar_Tc_Recheck.recompute_kind head)
in (
# 662 "FStar.ToSMT.Encode.fst"
let _50_959 = (FStar_Absyn_Util.kind_formals kk)
in (match (_50_959) with
| (formals, _50_958) -> begin
((FStar_List.length formals) = (FStar_List.length args))
end)))
end))
in (
# 664 "FStar.ToSMT.Encode.fst"
let head = (FStar_Absyn_Util.compress_typ head)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(
# 667 "FStar.ToSMT.Encode.fst"
let head = (lookup_typ_var env a)
in (
# 668 "FStar.ToSMT.Encode.fst"
let _50_966 = (encode_args args env)
in (match (_50_966) with
| (args, decls) -> begin
(
# 669 "FStar.ToSMT.Encode.fst"
let t = (mk_ApplyT_args head args)
in (t, decls))
end)))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(
# 673 "FStar.ToSMT.Encode.fst"
let _50_972 = (encode_args args env)
in (match (_50_972) with
| (args, decls) -> begin
if (is_full_app ()) then begin
(
# 675 "FStar.ToSMT.Encode.fst"
let head = (lookup_free_tvar_name env fv)
in (
# 676 "FStar.ToSMT.Encode.fst"
let t = (let _139_744 = (let _139_743 = (FStar_List.map (fun _50_10 -> (match (_50_10) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (head, _139_743))
in (FStar_ToSMT_Term.mkApp _139_744))
in (t, decls)))
end else begin
(
# 678 "FStar.ToSMT.Encode.fst"
let head = (lookup_free_tvar env fv)
in (
# 679 "FStar.ToSMT.Encode.fst"
let t = (mk_ApplyT_args head args)
in (t, decls)))
end
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(
# 683 "FStar.ToSMT.Encode.fst"
let ttm = (let _139_745 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _139_745))
in (
# 684 "FStar.ToSMT.Encode.fst"
let _50_988 = (encode_knd k env ttm)
in (match (_50_988) with
| (t_has_k, decls) -> begin
(
# 685 "FStar.ToSMT.Encode.fst"
let d = FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| _50_991 -> begin
(
# 689 "FStar.ToSMT.Encode.fst"
let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, body) -> begin
(
# 697 "FStar.ToSMT.Encode.fst"
let _50_1003 = (encode_binders None bs env)
in (match (_50_1003) with
| (vars, guards, env, decls, _50_1002) -> begin
(
# 698 "FStar.ToSMT.Encode.fst"
let _50_1006 = (encode_typ_term body env)
in (match (_50_1006) with
| (body, decls') -> begin
(
# 700 "FStar.ToSMT.Encode.fst"
let key_body = (let _139_749 = (let _139_748 = (let _139_747 = (let _139_746 = (FStar_ToSMT_Term.mk_and_l guards)
in (_139_746, body))
in (FStar_ToSMT_Term.mkImp _139_747))
in ([], vars, _139_748))
in (FStar_ToSMT_Term.mkForall _139_749))
in (
# 701 "FStar.ToSMT.Encode.fst"
let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (
# 702 "FStar.ToSMT.Encode.fst"
let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _50_1012, _50_1014) -> begin
(let _139_752 = (let _139_751 = (let _139_750 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _139_750))
in (FStar_ToSMT_Term.mkApp _139_751))
in (_139_752, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (head) -> begin
(head, [])
end
| None -> begin
(
# 714 "FStar.ToSMT.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 715 "FStar.ToSMT.Encode.fst"
let tsym = (varops.fresh "Typ_lam")
in (
# 716 "FStar.ToSMT.Encode.fst"
let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, None))
in (
# 717 "FStar.ToSMT.Encode.fst"
let t = (let _139_754 = (let _139_753 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _139_753))
in (FStar_ToSMT_Term.mkApp _139_754))
in (
# 718 "FStar.ToSMT.Encode.fst"
let app = (mk_ApplyT t vars)
in (
# 720 "FStar.ToSMT.Encode.fst"
let interp = (let _139_761 = (let _139_760 = (let _139_759 = (let _139_758 = (let _139_757 = (let _139_756 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _139_755 = (FStar_ToSMT_Term.mkEq (app, body))
in (_139_756, _139_755)))
in (FStar_ToSMT_Term.mkImp _139_757))
in (((app)::[])::[], (FStar_List.append vars cvars), _139_758))
in (FStar_ToSMT_Term.mkForall _139_759))
in (_139_760, Some ("Typ_lam interpretation")))
in FStar_ToSMT_Term.Assume (_139_761))
in (
# 723 "FStar.ToSMT.Encode.fst"
let kinding = (
# 724 "FStar.ToSMT.Encode.fst"
let _50_1029 = (let _139_762 = (FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _139_762 env t))
in (match (_50_1029) with
| (ktm, decls'') -> begin
(let _139_766 = (let _139_765 = (let _139_764 = (let _139_763 = (FStar_ToSMT_Term.mkForall (((t)::[])::[], cvars, ktm))
in (_139_763, Some ("Typ_lam kinding")))
in FStar_ToSMT_Term.Assume (_139_764))
in (_139_765)::[])
in (FStar_List.append decls'' _139_766))
end))
in (
# 727 "FStar.ToSMT.Encode.fst"
let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(interp)::kinding))
in (
# 729 "FStar.ToSMT.Encode.fst"
let _50_1032 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))
end)
end))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _50_1036) -> begin
(encode_typ_term t env)
end
| FStar_Absyn_Syntax.Typ_meta (_50_1040) -> begin
(let _139_767 = (FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _139_767 env))
end
| (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _139_772 = (let _139_771 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Absyn_Syntax.pos)
in (let _139_770 = (FStar_Absyn_Print.tag_of_typ t0)
in (let _139_769 = (FStar_Absyn_Print.typ_to_string t0)
in (let _139_768 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _139_771 _139_770 _139_769 _139_768)))))
in (FStar_All.failwith _139_772))
end)))
and encode_exp : FStar_Absyn_Syntax.exp  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun e env -> (
# 745 "FStar.ToSMT.Encode.fst"
let e = (FStar_Absyn_Visit.compress_exp_uvars e)
in (
# 746 "FStar.ToSMT.Encode.fst"
let e0 = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_50_1051) -> begin
(let _139_775 = (FStar_Absyn_Util.compress_exp e)
in (encode_exp _139_775 env))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(
# 752 "FStar.ToSMT.Encode.fst"
let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Absyn_Syntax.Exp_fvar (v, _50_1058) -> begin
(let _139_776 = (lookup_free_var env v)
in (_139_776, []))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _139_777 = (encode_const c)
in (_139_777, []))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _50_1066) -> begin
(
# 762 "FStar.ToSMT.Encode.fst"
let _50_1069 = (FStar_ST.op_Colon_Equals e.FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _50_1073)) -> begin
(encode_exp e env)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, _50_1079) -> begin
(
# 770 "FStar.ToSMT.Encode.fst"
let e = (let _139_778 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Exp_uvar _139_778))
in (e, []))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(
# 774 "FStar.ToSMT.Encode.fst"
let fallback = (fun _50_1088 -> (match (()) with
| () -> begin
(
# 775 "FStar.ToSMT.Encode.fst"
let f = (varops.fresh "Exp_abs")
in (
# 776 "FStar.ToSMT.Encode.fst"
let decl = FStar_ToSMT_Term.DeclFun ((f, [], FStar_ToSMT_Term.Term_sort, None))
in (let _139_781 = (FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
in (_139_781, (decl)::[]))))
end))
in (match ((FStar_ST.read e.FStar_Absyn_Syntax.tk)) with
| None -> begin
(
# 781 "FStar.ToSMT.Encode.fst"
let _50_1092 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
if (let _139_782 = (FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (FStar_All.pipe_left Prims.op_Negation _139_782)) then begin
(fallback ())
end else begin
(
# 786 "FStar.ToSMT.Encode.fst"
let tfun = (as_function_typ env tfun)
in (match (tfun.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(
# 789 "FStar.ToSMT.Encode.fst"
let nformals = (FStar_List.length bs')
in if ((nformals < (FStar_List.length bs)) && (FStar_Absyn_Util.is_total_comp c)) then begin
(
# 798 "FStar.ToSMT.Encode.fst"
let _50_1104 = (FStar_Util.first_N nformals bs)
in (match (_50_1104) with
| (bs0, rest) -> begin
(
# 799 "FStar.ToSMT.Encode.fst"
let res_t = (match ((FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s (FStar_Absyn_Util.comp_result c))
end
| _50_1108 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 802 "FStar.ToSMT.Encode.fst"
let e = (let _139_784 = (let _139_783 = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.FStar_Absyn_Syntax.pos)
in (bs0, _139_783))
in (FStar_Absyn_Syntax.mk_Exp_abs _139_784 (Some (tfun)) e0.FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end else begin
(
# 807 "FStar.ToSMT.Encode.fst"
let _50_1117 = (encode_binders None bs env)
in (match (_50_1117) with
| (vars, guards, envbody, decls, _50_1116) -> begin
(
# 808 "FStar.ToSMT.Encode.fst"
let _50_1120 = (encode_exp body envbody)
in (match (_50_1120) with
| (body, decls') -> begin
(
# 810 "FStar.ToSMT.Encode.fst"
let key_body = (let _139_788 = (let _139_787 = (let _139_786 = (let _139_785 = (FStar_ToSMT_Term.mk_and_l guards)
in (_139_785, body))
in (FStar_ToSMT_Term.mkImp _139_786))
in ([], vars, _139_787))
in (FStar_ToSMT_Term.mkForall _139_788))
in (
# 811 "FStar.ToSMT.Encode.fst"
let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (
# 812 "FStar.ToSMT.Encode.fst"
let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _50_1126, _50_1128) -> begin
(let _139_791 = (let _139_790 = (let _139_789 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _139_789))
in (FStar_ToSMT_Term.mkApp _139_790))
in (_139_791, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
(t, [])
end
| None -> begin
(
# 823 "FStar.ToSMT.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 824 "FStar.ToSMT.Encode.fst"
let fsym = (varops.fresh "Exp_abs")
in (
# 825 "FStar.ToSMT.Encode.fst"
let fdecl = FStar_ToSMT_Term.DeclFun ((fsym, cvar_sorts, FStar_ToSMT_Term.Term_sort, None))
in (
# 826 "FStar.ToSMT.Encode.fst"
let f = (let _139_793 = (let _139_792 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _139_792))
in (FStar_ToSMT_Term.mkApp _139_793))
in (
# 827 "FStar.ToSMT.Encode.fst"
let app = (mk_ApplyE f vars)
in (
# 829 "FStar.ToSMT.Encode.fst"
let _50_1142 = (encode_typ_pred None tfun env f)
in (match (_50_1142) with
| (f_has_t, decls'') -> begin
(
# 830 "FStar.ToSMT.Encode.fst"
let typing_f = (let _139_795 = (let _139_794 = (FStar_ToSMT_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_139_794, Some ((Prims.strcat fsym " typing"))))
in FStar_ToSMT_Term.Assume (_139_795))
in (
# 833 "FStar.ToSMT.Encode.fst"
let interp_f = (let _139_802 = (let _139_801 = (let _139_800 = (let _139_799 = (let _139_798 = (let _139_797 = (FStar_ToSMT_Term.mk_IsTyped app)
in (let _139_796 = (FStar_ToSMT_Term.mkEq (app, body))
in (_139_797, _139_796)))
in (FStar_ToSMT_Term.mkImp _139_798))
in (((app)::[])::[], (FStar_List.append vars cvars), _139_799))
in (FStar_ToSMT_Term.mkForall _139_800))
in (_139_801, Some ((Prims.strcat fsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_139_802))
in (
# 836 "FStar.ToSMT.Encode.fst"
let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (
# 838 "FStar.ToSMT.Encode.fst"
let _50_1146 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end)))))))
end)
end))))
end))
end))
end)
end
| _50_1149 -> begin
(FStar_All.failwith "Impossible")
end))
end
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (l, _50_1160); FStar_Absyn_Syntax.tk = _50_1157; FStar_Absyn_Syntax.pos = _50_1155; FStar_Absyn_Syntax.fvs = _50_1153; FStar_Absyn_Syntax.uvs = _50_1151}, (FStar_Util.Inl (_50_1175), _50_1178)::(FStar_Util.Inr (v1), _50_1172)::(FStar_Util.Inr (v2), _50_1167)::[]) when (FStar_Ident.lid_equals l.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
(
# 848 "FStar.ToSMT.Encode.fst"
let _50_1185 = (encode_exp v1 env)
in (match (_50_1185) with
| (v1, decls1) -> begin
(
# 849 "FStar.ToSMT.Encode.fst"
let _50_1188 = (encode_exp v2 env)
in (match (_50_1188) with
| (v2, decls2) -> begin
(let _139_803 = (FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_139_803, (FStar_List.append decls1 decls2)))
end))
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_50_1198); FStar_Absyn_Syntax.tk = _50_1196; FStar_Absyn_Syntax.pos = _50_1194; FStar_Absyn_Syntax.fvs = _50_1192; FStar_Absyn_Syntax.uvs = _50_1190}, _50_1202) -> begin
(let _139_804 = (whnf_e env e)
in (encode_exp _139_804 env))
end
| FStar_Absyn_Syntax.Exp_app (head, args_e) -> begin
(
# 856 "FStar.ToSMT.Encode.fst"
let _50_1211 = (encode_args args_e env)
in (match (_50_1211) with
| (args, decls) -> begin
(
# 858 "FStar.ToSMT.Encode.fst"
let encode_partial_app = (fun ht_opt -> (
# 859 "FStar.ToSMT.Encode.fst"
let _50_1216 = (encode_exp head env)
in (match (_50_1216) with
| (head, decls') -> begin
(
# 860 "FStar.ToSMT.Encode.fst"
let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(
# 864 "FStar.ToSMT.Encode.fst"
let _50_1225 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_50_1225) with
| (formals, rest) -> begin
(
# 865 "FStar.ToSMT.Encode.fst"
let subst = (FStar_Absyn_Util.formals_for_actuals formals args_e)
in (
# 866 "FStar.ToSMT.Encode.fst"
let ty = (let _139_807 = (FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (FStar_Absyn_Syntax.ktype)) e0.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _139_807 (FStar_Absyn_Util.subst_typ subst)))
in (
# 867 "FStar.ToSMT.Encode.fst"
let _50_1230 = (encode_typ_pred None ty env app_tm)
in (match (_50_1230) with
| (has_type, decls'') -> begin
(
# 868 "FStar.ToSMT.Encode.fst"
let cvars = (FStar_ToSMT_Term.free_variables has_type)
in (
# 869 "FStar.ToSMT.Encode.fst"
let e_typing = (let _139_809 = (let _139_808 = (FStar_ToSMT_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_139_808, None))
in FStar_ToSMT_Term.Assume (_139_809))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (
# 873 "FStar.ToSMT.Encode.fst"
let encode_full_app = (fun fv -> (
# 874 "FStar.ToSMT.Encode.fst"
let _50_1237 = (lookup_free_var_sym env fv)
in (match (_50_1237) with
| (fname, fuel_args) -> begin
(
# 875 "FStar.ToSMT.Encode.fst"
let tm = (let _139_815 = (let _139_814 = (let _139_813 = (FStar_List.map (fun _50_11 -> (match (_50_11) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (FStar_List.append fuel_args _139_813))
in (fname, _139_814))
in (FStar_ToSMT_Term.mkApp' _139_815))
in (tm, decls))
end)))
in (
# 878 "FStar.ToSMT.Encode.fst"
let head = (FStar_Absyn_Util.compress_exp head)
in (
# 880 "FStar.ToSMT.Encode.fst"
let _50_1244 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("186"))) then begin
(let _139_817 = (FStar_Absyn_Print.exp_to_string head)
in (let _139_816 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.print2 "Recomputing type for %s\nFull term is %s\n" _139_817 _139_816)))
end else begin
()
end
in (
# 883 "FStar.ToSMT.Encode.fst"
let head_type = (let _139_820 = (let _139_819 = (let _139_818 = (FStar_Tc_Recheck.recompute_typ head)
in (FStar_Absyn_Util.unrefine _139_818))
in (whnf env _139_819))
in (FStar_All.pipe_left FStar_Absyn_Util.unrefine _139_820))
in (
# 885 "FStar.ToSMT.Encode.fst"
let _50_1247 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _139_823 = (FStar_Absyn_Print.exp_to_string head)
in (let _139_822 = (FStar_Absyn_Print.tag_of_exp head)
in (let _139_821 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.print3 "Recomputed type of head %s (%s) to be %s\n" _139_823 _139_822 _139_821))))
end else begin
()
end
in (match ((FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _139_827 = (let _139_826 = (FStar_Range.string_of_range e0.FStar_Absyn_Syntax.pos)
in (let _139_825 = (FStar_Absyn_Print.exp_to_string e0)
in (let _139_824 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.format3 "(%s) term is %s; head type is %s\n" _139_826 _139_825 _139_824))))
in (FStar_All.failwith _139_827))
end
| Some (formals, c) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _50_1256) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _50_1260 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some ((formals, c))))
end else begin
(encode_partial_app None)
end
end)
end)))))))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_50_1269); FStar_Absyn_Syntax.lbtyp = _50_1267; FStar_Absyn_Syntax.lbeff = _50_1265; FStar_Absyn_Syntax.lbdef = _50_1263}::[]), _50_1275) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = t1; FStar_Absyn_Syntax.lbeff = _50_1281; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 905 "FStar.ToSMT.Encode.fst"
let _50_1293 = (encode_exp e1 env)
in (match (_50_1293) with
| (ee1, decls1) -> begin
(
# 906 "FStar.ToSMT.Encode.fst"
let env' = (push_term_var env x ee1)
in (
# 907 "FStar.ToSMT.Encode.fst"
let _50_1297 = (encode_exp e2 env')
in (match (_50_1297) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let (_50_1299) -> begin
(
# 911 "FStar.ToSMT.Encode.fst"
let _50_1301 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (
# 912 "FStar.ToSMT.Encode.fst"
let e = (varops.fresh "let-rec")
in (
# 913 "FStar.ToSMT.Encode.fst"
let decl_e = FStar_ToSMT_Term.DeclFun ((e, [], FStar_ToSMT_Term.Term_sort, None))
in (let _139_828 = (FStar_ToSMT_Term.mkFreeV (e, FStar_ToSMT_Term.Term_sort))
in (_139_828, (decl_e)::[])))))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(
# 917 "FStar.ToSMT.Encode.fst"
let _50_1311 = (encode_exp e env)
in (match (_50_1311) with
| (scr, decls) -> begin
(
# 920 "FStar.ToSMT.Encode.fst"
let _50_1351 = (FStar_List.fold_right (fun _50_1315 _50_1318 -> (match ((_50_1315, _50_1318)) with
| ((p, w, br), (else_case, decls)) -> begin
(
# 921 "FStar.ToSMT.Encode.fst"
let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _50_1322 _50_1325 -> (match ((_50_1322, _50_1325)) with
| ((env0, pattern), (else_case, decls)) -> begin
(
# 923 "FStar.ToSMT.Encode.fst"
let guard = (pattern.guard scr)
in (
# 924 "FStar.ToSMT.Encode.fst"
let projections = (pattern.projections scr)
in (
# 925 "FStar.ToSMT.Encode.fst"
let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _50_1331 -> (match (_50_1331) with
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
# 928 "FStar.ToSMT.Encode.fst"
let _50_1345 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(
# 931 "FStar.ToSMT.Encode.fst"
let _50_1342 = (encode_exp w env)
in (match (_50_1342) with
| (w, decls2) -> begin
(let _139_839 = (let _139_838 = (let _139_837 = (let _139_836 = (let _139_835 = (FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
in (w, _139_835))
in (FStar_ToSMT_Term.mkEq _139_836))
in (guard, _139_837))
in (FStar_ToSMT_Term.mkAnd _139_838))
in (_139_839, decls2))
end))
end)
in (match (_50_1345) with
| (guard, decls2) -> begin
(
# 933 "FStar.ToSMT.Encode.fst"
let _50_1348 = (encode_exp br env)
in (match (_50_1348) with
| (br, decls3) -> begin
(let _139_840 = (FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_139_840, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end)) pats (FStar_ToSMT_Term.mk_Term_unit, decls))
in (match (_50_1351) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (_50_1353) -> begin
(let _139_843 = (let _139_842 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _139_841 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "(%s): Impossible: encode_exp got %s" _139_842 _139_841)))
in (FStar_All.failwith _139_843))
end))))
and encode_pat : env_t  ->  FStar_Absyn_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _50_1360 -> begin
(let _139_846 = (encode_one_pat env pat)
in (_139_846)::[])
end))
and encode_one_pat : env_t  ->  FStar_Absyn_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (
# 948 "FStar.ToSMT.Encode.fst"
let _50_1363 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _139_849 = (FStar_Absyn_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _139_849))
end else begin
()
end
in (
# 949 "FStar.ToSMT.Encode.fst"
let _50_1367 = (FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_50_1367) with
| (vars, pat_exp_or_typ) -> begin
(
# 951 "FStar.ToSMT.Encode.fst"
let _50_1388 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _50_1370 v -> (match (_50_1370) with
| (env, vars) -> begin
(match (v) with
| FStar_Util.Inl (a) -> begin
(
# 953 "FStar.ToSMT.Encode.fst"
let _50_1378 = (gen_typ_var env a.FStar_Absyn_Syntax.v)
in (match (_50_1378) with
| (aa, _50_1376, env) -> begin
(env, ((v, (aa, FStar_ToSMT_Term.Type_sort)))::vars)
end))
end
| FStar_Util.Inr (x) -> begin
(
# 956 "FStar.ToSMT.Encode.fst"
let _50_1385 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_50_1385) with
| (xx, _50_1383, env) -> begin
(env, ((v, (xx, FStar_ToSMT_Term.Term_sort)))::vars)
end))
end)
end)) (env, [])))
in (match (_50_1388) with
| (env, vars) -> begin
(
# 959 "FStar.ToSMT.Encode.fst"
let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_50_1393) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
FStar_ToSMT_Term.mkTrue
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _139_857 = (let _139_856 = (encode_const c)
in (scrutinee, _139_856))
in (FStar_ToSMT_Term.mkEq _139_857))
end
| FStar_Absyn_Syntax.Pat_cons (f, _50_1417, args) -> begin
(
# 970 "FStar.ToSMT.Encode.fst"
let is_f = (mk_data_tester env f.FStar_Absyn_Syntax.v scrutinee)
in (
# 971 "FStar.ToSMT.Encode.fst"
let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _50_1426 -> (match (_50_1426) with
| (arg, _50_1425) -> begin
(
# 972 "FStar.ToSMT.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _139_860 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _139_860)))
end))))
in (FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (
# 976 "FStar.ToSMT.Encode.fst"
let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_50_1433) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _)) | (FStar_Absyn_Syntax.Pat_var (x)) | (FStar_Absyn_Syntax.Pat_wild (x)) -> begin
((FStar_Util.Inr (x), scrutinee))::[]
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _)) | (FStar_Absyn_Syntax.Pat_tvar (a)) | (FStar_Absyn_Syntax.Pat_twild (a)) -> begin
((FStar_Util.Inl (a), scrutinee))::[]
end
| FStar_Absyn_Syntax.Pat_constant (_50_1450) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_cons (f, _50_1454, args) -> begin
(let _139_868 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _50_1462 -> (match (_50_1462) with
| (arg, _50_1461) -> begin
(
# 992 "FStar.ToSMT.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _139_867 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _139_867)))
end))))
in (FStar_All.pipe_right _139_868 FStar_List.flatten))
end))
in (
# 996 "FStar.ToSMT.Encode.fst"
let pat_term = (fun _50_1465 -> (match (()) with
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
# 1000 "FStar.ToSMT.Encode.fst"
let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args : FStar_Absyn_Syntax.args  ->  env_t  ->  ((FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list * FStar_ToSMT_Term.decls_t) = (fun l env -> (
# 1010 "FStar.ToSMT.Encode.fst"
let _50_1495 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _50_1475 x -> (match (_50_1475) with
| (tms, decls) -> begin
(match (x) with
| (FStar_Util.Inl (t), _50_1480) -> begin
(
# 1011 "FStar.ToSMT.Encode.fst"
let _50_1484 = (encode_typ_term t env)
in (match (_50_1484) with
| (t, decls') -> begin
((FStar_Util.Inl (t))::tms, (FStar_List.append decls decls'))
end))
end
| (FStar_Util.Inr (e), _50_1488) -> begin
(
# 1012 "FStar.ToSMT.Encode.fst"
let _50_1492 = (encode_exp e env)
in (match (_50_1492) with
| (t, decls') -> begin
((FStar_Util.Inr (t))::tms, (FStar_List.append decls decls'))
end))
end)
end)) ([], [])))
in (match (_50_1495) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_formula : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun phi env -> (
# 1016 "FStar.ToSMT.Encode.fst"
let _50_1501 = (encode_formula_with_labels phi env)
in (match (_50_1501) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _50_1504 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.exp Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun induction_on new_pats t env -> (
# 1023 "FStar.ToSMT.Encode.fst"
let rec list_elements = (fun e -> (match ((let _139_883 = (FStar_Absyn_Util.unmeta_exp e)
in _139_883.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_1521); FStar_Absyn_Syntax.tk = _50_1518; FStar_Absyn_Syntax.pos = _50_1516; FStar_Absyn_Syntax.fvs = _50_1514; FStar_Absyn_Syntax.uvs = _50_1512}, _50_1526) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.nil_lid) -> begin
[]
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_1539); FStar_Absyn_Syntax.tk = _50_1536; FStar_Absyn_Syntax.pos = _50_1534; FStar_Absyn_Syntax.fvs = _50_1532; FStar_Absyn_Syntax.uvs = _50_1530}, _50_1554::(FStar_Util.Inr (hd), _50_1551)::(FStar_Util.Inr (tl), _50_1546)::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(let _139_884 = (list_elements tl)
in (hd)::_139_884)
end
| _50_1559 -> begin
(
# 1027 "FStar.ToSMT.Encode.fst"
let _50_1560 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (
# 1029 "FStar.ToSMT.Encode.fst"
let v_or_t_pat = (fun p -> (match ((let _139_887 = (FStar_Absyn_Util.unmeta_exp p)
in _139_887.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_1574); FStar_Absyn_Syntax.tk = _50_1571; FStar_Absyn_Syntax.pos = _50_1569; FStar_Absyn_Syntax.fvs = _50_1567; FStar_Absyn_Syntax.uvs = _50_1565}, (FStar_Util.Inl (_50_1584), _50_1587)::(FStar_Util.Inr (e), _50_1581)::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpat_lid) -> begin
(FStar_Absyn_Syntax.varg e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_1602); FStar_Absyn_Syntax.tk = _50_1599; FStar_Absyn_Syntax.pos = _50_1597; FStar_Absyn_Syntax.fvs = _50_1595; FStar_Absyn_Syntax.uvs = _50_1593}, (FStar_Util.Inl (t), _50_1609)::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatT_lid) -> begin
(FStar_Absyn_Syntax.targ t)
end
| _50_1615 -> begin
(FStar_All.failwith "Unexpected pattern term")
end))
in (
# 1034 "FStar.ToSMT.Encode.fst"
let lemma_pats = (fun p -> (
# 1035 "FStar.ToSMT.Encode.fst"
let elts = (list_elements p)
in (match (elts) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _50_1637); FStar_Absyn_Syntax.tk = _50_1634; FStar_Absyn_Syntax.pos = _50_1632; FStar_Absyn_Syntax.fvs = _50_1630; FStar_Absyn_Syntax.uvs = _50_1628}, (FStar_Util.Inr (e), _50_1644)::[]); FStar_Absyn_Syntax.tk = _50_1626; FStar_Absyn_Syntax.pos = _50_1624; FStar_Absyn_Syntax.fvs = _50_1622; FStar_Absyn_Syntax.uvs = _50_1620}::[] when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatOr_lid) -> begin
(let _139_892 = (list_elements e)
in (FStar_All.pipe_right _139_892 (FStar_List.map (fun branch -> (let _139_891 = (list_elements branch)
in (FStar_All.pipe_right _139_891 (FStar_List.map v_or_t_pat)))))))
end
| _50_1653 -> begin
(let _139_893 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_139_893)::[])
end)))
in (
# 1046 "FStar.ToSMT.Encode.fst"
let _50_1696 = (match ((let _139_894 = (FStar_Absyn_Util.compress_typ t)
in _139_894.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (ct); FStar_Absyn_Syntax.tk = _50_1662; FStar_Absyn_Syntax.pos = _50_1660; FStar_Absyn_Syntax.fvs = _50_1658; FStar_Absyn_Syntax.uvs = _50_1656}) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (pre), _50_1681)::(FStar_Util.Inl (post), _50_1676)::(FStar_Util.Inr (pats), _50_1671)::[] -> begin
(
# 1050 "FStar.ToSMT.Encode.fst"
let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _139_895 = (lemma_pats pats')
in (binders, pre, post, _139_895)))
end
| _50_1689 -> begin
(FStar_All.failwith "impos")
end)
end
| _50_1691 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_50_1696) with
| (binders, pre, post, patterns) -> begin
(
# 1058 "FStar.ToSMT.Encode.fst"
let _50_1703 = (encode_binders None binders env)
in (match (_50_1703) with
| (vars, guards, env, decls, _50_1702) -> begin
(
# 1061 "FStar.ToSMT.Encode.fst"
let _50_1723 = (let _139_899 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (
# 1062 "FStar.ToSMT.Encode.fst"
let _50_1720 = (let _139_898 = (FStar_All.pipe_right branch (FStar_List.map (fun _50_12 -> (match (_50_12) with
| (FStar_Util.Inl (t), _50_1709) -> begin
(encode_formula t env)
end
| (FStar_Util.Inr (e), _50_1714) -> begin
(encode_exp e (
# 1064 "FStar.ToSMT.Encode.fst"
let _50_1716 = env
in {bindings = _50_1716.bindings; depth = _50_1716.depth; tcenv = _50_1716.tcenv; warn = _50_1716.warn; cache = _50_1716.cache; nolabels = _50_1716.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _50_1716.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _139_898 FStar_List.unzip))
in (match (_50_1720) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _139_899 FStar_List.unzip))
in (match (_50_1723) with
| (pats, decls') -> begin
(
# 1067 "FStar.ToSMT.Encode.fst"
let decls' = (FStar_List.flatten decls')
in (
# 1069 "FStar.ToSMT.Encode.fst"
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _139_902 = (let _139_901 = (FStar_ToSMT_Term.mkFreeV l)
in (FStar_ToSMT_Term.mk_Precedes _139_901 e))
in (_139_902)::p))))
end
| _50_1733 -> begin
(
# 1077 "FStar.ToSMT.Encode.fst"
let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _139_908 = (FStar_ToSMT_Term.mk_Precedes tl e)
in (_139_908)::p))))
end
| (x, FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _139_910 = (let _139_909 = (FStar_ToSMT_Term.mkFreeV (x, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_LexCons _139_909 tl))
in (aux _139_910 vars))
end
| _50_1745 -> begin
pats
end))
in (let _139_911 = (FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", FStar_ToSMT_Term.Term_sort))
in (aux _139_911 vars)))
end)
end)
in (
# 1084 "FStar.ToSMT.Encode.fst"
let env = (
# 1084 "FStar.ToSMT.Encode.fst"
let _50_1747 = env
in {bindings = _50_1747.bindings; depth = _50_1747.depth; tcenv = _50_1747.tcenv; warn = _50_1747.warn; cache = _50_1747.cache; nolabels = true; use_zfuel_name = _50_1747.use_zfuel_name; encode_non_total_function_typ = _50_1747.encode_non_total_function_typ})
in (
# 1085 "FStar.ToSMT.Encode.fst"
let _50_1752 = (let _139_912 = (FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _139_912 env))
in (match (_50_1752) with
| (pre, decls'') -> begin
(
# 1086 "FStar.ToSMT.Encode.fst"
let _50_1755 = (let _139_913 = (FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _139_913 env))
in (match (_50_1755) with
| (post, decls''') -> begin
(
# 1087 "FStar.ToSMT.Encode.fst"
let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _139_918 = (let _139_917 = (let _139_916 = (let _139_915 = (let _139_914 = (FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_139_914, post))
in (FStar_ToSMT_Term.mkImp _139_915))
in (pats, vars, _139_916))
in (FStar_ToSMT_Term.mkForall _139_917))
in (_139_918, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula_with_labels : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * labels * FStar_ToSMT_Term.decls_t) = (fun phi env -> (
# 1091 "FStar.ToSMT.Encode.fst"
let enc = (fun f l -> (
# 1092 "FStar.ToSMT.Encode.fst"
let _50_1776 = (FStar_Util.fold_map (fun decls x -> (match ((Prims.fst x)) with
| FStar_Util.Inl (t) -> begin
(
# 1093 "FStar.ToSMT.Encode.fst"
let _50_1768 = (encode_typ_term t env)
in (match (_50_1768) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))
end
| FStar_Util.Inr (e) -> begin
(
# 1094 "FStar.ToSMT.Encode.fst"
let _50_1773 = (encode_exp e env)
in (match (_50_1773) with
| (e, decls') -> begin
((FStar_List.append decls decls'), e)
end))
end)) [] l)
in (match (_50_1776) with
| (decls, args) -> begin
(let _139_936 = (f args)
in (_139_936, [], decls))
end)))
in (
# 1097 "FStar.ToSMT.Encode.fst"
let enc_prop_c = (fun f l -> (
# 1098 "FStar.ToSMT.Encode.fst"
let _50_1796 = (FStar_List.fold_right (fun t _50_1784 -> (match (_50_1784) with
| (phis, labs, decls) -> begin
(match ((Prims.fst t)) with
| FStar_Util.Inl (t) -> begin
(
# 1102 "FStar.ToSMT.Encode.fst"
let _50_1790 = (encode_formula_with_labels t env)
in (match (_50_1790) with
| (phi, labs', decls') -> begin
((phi)::phis, (FStar_List.append labs' labs), (FStar_List.append decls' decls))
end))
end
| _50_1792 -> begin
(FStar_All.failwith "Expected a formula")
end)
end)) l ([], [], []))
in (match (_50_1796) with
| (phis, labs, decls) -> begin
(let _139_952 = (f phis)
in (_139_952, labs, decls))
end)))
in (
# 1109 "FStar.ToSMT.Encode.fst"
let const_op = (fun f _50_1799 -> (f, [], []))
in (
# 1110 "FStar.ToSMT.Encode.fst"
let un_op = (fun f l -> (let _139_966 = (FStar_List.hd l)
in (FStar_All.pipe_left f _139_966)))
in (
# 1111 "FStar.ToSMT.Encode.fst"
let bin_op = (fun f _50_13 -> (match (_50_13) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _50_1810 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 1114 "FStar.ToSMT.Encode.fst"
let eq_op = (fun _50_14 -> (match (_50_14) with
| _50_1818::_50_1816::e1::e2::[] -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) l)
end))
in (
# 1118 "FStar.ToSMT.Encode.fst"
let mk_imp = (fun _50_15 -> (match (_50_15) with
| (FStar_Util.Inl (lhs), _50_1831)::(FStar_Util.Inl (rhs), _50_1826)::[] -> begin
(
# 1120 "FStar.ToSMT.Encode.fst"
let _50_1837 = (encode_formula_with_labels rhs env)
in (match (_50_1837) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _50_1840) -> begin
(l1, labs1, decls1)
end
| _50_1844 -> begin
(
# 1124 "FStar.ToSMT.Encode.fst"
let _50_1848 = (encode_formula_with_labels lhs env)
in (match (_50_1848) with
| (l2, labs2, decls2) -> begin
(let _139_980 = (FStar_ToSMT_Term.mkImp (l2, l1))
in (_139_980, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _50_1850 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1129 "FStar.ToSMT.Encode.fst"
let mk_ite = (fun _50_16 -> (match (_50_16) with
| (FStar_Util.Inl (guard), _50_1866)::(FStar_Util.Inl (_then), _50_1861)::(FStar_Util.Inl (_else), _50_1856)::[] -> begin
(
# 1131 "FStar.ToSMT.Encode.fst"
let _50_1872 = (encode_formula_with_labels guard env)
in (match (_50_1872) with
| (g, labs1, decls1) -> begin
(
# 1132 "FStar.ToSMT.Encode.fst"
let _50_1876 = (encode_formula_with_labels _then env)
in (match (_50_1876) with
| (t, labs2, decls2) -> begin
(
# 1133 "FStar.ToSMT.Encode.fst"
let _50_1880 = (encode_formula_with_labels _else env)
in (match (_50_1880) with
| (e, labs3, decls3) -> begin
(
# 1134 "FStar.ToSMT.Encode.fst"
let res = (FStar_ToSMT_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append labs1 labs2) labs3), (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _50_1883 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1139 "FStar.ToSMT.Encode.fst"
let unboxInt_l = (fun f l -> (let _139_992 = (FStar_List.map FStar_ToSMT_Term.unboxInt l)
in (f _139_992)))
in (
# 1140 "FStar.ToSMT.Encode.fst"
let connectives = (let _139_1053 = (let _139_1001 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkAnd))
in (FStar_Absyn_Const.and_lid, _139_1001))
in (let _139_1052 = (let _139_1051 = (let _139_1007 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkOr))
in (FStar_Absyn_Const.or_lid, _139_1007))
in (let _139_1050 = (let _139_1049 = (let _139_1048 = (let _139_1016 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkIff))
in (FStar_Absyn_Const.iff_lid, _139_1016))
in (let _139_1047 = (let _139_1046 = (let _139_1045 = (let _139_1025 = (FStar_All.pipe_left enc_prop_c (un_op FStar_ToSMT_Term.mkNot))
in (FStar_Absyn_Const.not_lid, _139_1025))
in (let _139_1044 = (let _139_1043 = (let _139_1031 = (FStar_All.pipe_left enc (bin_op FStar_ToSMT_Term.mkEq))
in (FStar_Absyn_Const.eqT_lid, _139_1031))
in (_139_1043)::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op FStar_ToSMT_Term.mkTrue)))::((FStar_Absyn_Const.false_lid, (const_op FStar_ToSMT_Term.mkFalse)))::[])
in (_139_1045)::_139_1044))
in ((FStar_Absyn_Const.ite_lid, mk_ite))::_139_1046)
in (_139_1048)::_139_1047))
in ((FStar_Absyn_Const.imp_lid, mk_imp))::_139_1049)
in (_139_1051)::_139_1050))
in (_139_1053)::_139_1052))
in (
# 1153 "FStar.ToSMT.Encode.fst"
let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (phi', msg, r, b)) -> begin
(
# 1155 "FStar.ToSMT.Encode.fst"
let _50_1901 = (encode_formula_with_labels phi' env)
in (match (_50_1901) with
| (phi, labs, decls) -> begin
if env.nolabels then begin
(phi, [], decls)
end else begin
(
# 1158 "FStar.ToSMT.Encode.fst"
let lvar = (let _139_1056 = (varops.fresh "label")
in (_139_1056, FStar_ToSMT_Term.Bool_sort))
in (
# 1159 "FStar.ToSMT.Encode.fst"
let lterm = (FStar_ToSMT_Term.mkFreeV lvar)
in (
# 1160 "FStar.ToSMT.Encode.fst"
let lphi = (FStar_ToSMT_Term.mkOr (lterm, phi))
in (lphi, ((lvar, msg, r))::labs, decls))))
end
end))
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _50_1912; FStar_Absyn_Syntax.pos = _50_1910; FStar_Absyn_Syntax.fvs = _50_1908; FStar_Absyn_Syntax.uvs = _50_1906}, _50_1927::(FStar_Util.Inr (l), _50_1924)::(FStar_Util.Inl (phi), _50_1919)::[]) when (FStar_Ident.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_IH) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(
# 1165 "FStar.ToSMT.Encode.fst"
let _50_1933 = (encode_exp l env)
in (match (_50_1933) with
| (e, decls) -> begin
(
# 1166 "FStar.ToSMT.Encode.fst"
let _50_1936 = (encode_function_type_as_formula (Some (e)) None phi env)
in (match (_50_1936) with
| (f, decls') -> begin
(f, [], (FStar_List.append decls decls'))
end))
end))
end else begin
(FStar_ToSMT_Term.mkTrue, [], [])
end
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _50_1944; FStar_Absyn_Syntax.pos = _50_1942; FStar_Absyn_Syntax.fvs = _50_1940; FStar_Absyn_Syntax.uvs = _50_1938}, _50_1956::(FStar_Util.Inl (phi), _50_1952)::tl) when (FStar_Ident.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_lem) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(
# 1173 "FStar.ToSMT.Encode.fst"
let pat = (match (tl) with
| [] -> begin
None
end
| (FStar_Util.Inr (pat), _50_1964)::[] -> begin
Some (pat)
end)
in (
# 1176 "FStar.ToSMT.Encode.fst"
let _50_1970 = (encode_function_type_as_formula None pat phi env)
in (match (_50_1970) with
| (f, decls) -> begin
(f, [], decls)
end)))
end else begin
(FStar_ToSMT_Term.mkTrue, [], [])
end
end
| _50_1972 -> begin
(
# 1181 "FStar.ToSMT.Encode.fst"
let _50_1975 = (encode_typ_term phi env)
in (match (_50_1975) with
| (tt, decls) -> begin
(let _139_1057 = (FStar_ToSMT_Term.mk_Valid tt)
in (_139_1057, [], decls))
end))
end))
in (
# 1184 "FStar.ToSMT.Encode.fst"
let encode_q_body = (fun env bs ps body -> (
# 1185 "FStar.ToSMT.Encode.fst"
let _50_1987 = (encode_binders None bs env)
in (match (_50_1987) with
| (vars, guards, env, decls, _50_1986) -> begin
(
# 1186 "FStar.ToSMT.Encode.fst"
let _50_2007 = (let _139_1069 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (
# 1187 "FStar.ToSMT.Encode.fst"
let _50_2004 = (let _139_1068 = (FStar_All.pipe_right p (FStar_List.map (fun _50_17 -> (match (_50_17) with
| (FStar_Util.Inl (t), _50_1993) -> begin
(encode_typ_term t env)
end
| (FStar_Util.Inr (e), _50_1998) -> begin
(encode_exp e (
# 1189 "FStar.ToSMT.Encode.fst"
let _50_2000 = env
in {bindings = _50_2000.bindings; depth = _50_2000.depth; tcenv = _50_2000.tcenv; warn = _50_2000.warn; cache = _50_2000.cache; nolabels = _50_2000.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _50_2000.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _139_1068 FStar_List.unzip))
in (match (_50_2004) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _139_1069 FStar_List.unzip))
in (match (_50_2007) with
| (pats, decls') -> begin
(
# 1191 "FStar.ToSMT.Encode.fst"
let _50_2011 = (encode_formula_with_labels body env)
in (match (_50_2011) with
| (body, labs, decls'') -> begin
(let _139_1070 = (FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _139_1070, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (
# 1194 "FStar.ToSMT.Encode.fst"
let _50_2012 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _139_1071 = (FStar_Absyn_Print.formula_to_string phi)
in (FStar_Util.print1 ">>>> Destructing as formula ... %s\n" _139_1071))
end else begin
()
end
in (
# 1196 "FStar.ToSMT.Encode.fst"
let phi = (FStar_Absyn_Util.compress_typ phi)
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _50_2024 -> (match (_50_2024) with
| (l, _50_2023) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_50_2027, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, pats, body)) -> begin
(
# 1206 "FStar.ToSMT.Encode.fst"
let _50_2037 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _139_1088 = (FStar_All.pipe_right vars (FStar_Absyn_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _139_1088))
end else begin
()
end
in (
# 1209 "FStar.ToSMT.Encode.fst"
let _50_2045 = (encode_q_body env vars pats body)
in (match (_50_2045) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _139_1091 = (let _139_1090 = (let _139_1089 = (FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _139_1089))
in (FStar_ToSMT_Term.mkForall _139_1090))
in (_139_1091, labs, decls))
end)))
end
| Some (FStar_Absyn_Util.QEx (vars, pats, body)) -> begin
(
# 1213 "FStar.ToSMT.Encode.fst"
let _50_2058 = (encode_q_body env vars pats body)
in (match (_50_2058) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _139_1094 = (let _139_1093 = (let _139_1092 = (FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _139_1092))
in (FStar_ToSMT_Term.mkExists _139_1093))
in (_139_1094, labs, decls))
end))
end))))))))))))))))

# 1222 "FStar.ToSMT.Encode.fst"
type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}

# 1222 "FStar.ToSMT.Encode.fst"
let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))

# 1228 "FStar.ToSMT.Encode.fst"
let prims : prims_t = (
# 1229 "FStar.ToSMT.Encode.fst"
let _50_2064 = (fresh_fvar "a" FStar_ToSMT_Term.Type_sort)
in (match (_50_2064) with
| (asym, a) -> begin
(
# 1230 "FStar.ToSMT.Encode.fst"
let _50_2067 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_50_2067) with
| (xsym, x) -> begin
(
# 1231 "FStar.ToSMT.Encode.fst"
let _50_2070 = (fresh_fvar "y" FStar_ToSMT_Term.Term_sort)
in (match (_50_2070) with
| (ysym, y) -> begin
(
# 1232 "FStar.ToSMT.Encode.fst"
let deffun = (fun vars body x -> (let _139_1129 = (let _139_1128 = (let _139_1127 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _139_1126 = (FStar_ToSMT_Term.abstr vars body)
in (x, _139_1127, FStar_ToSMT_Term.Term_sort, _139_1126, None)))
in FStar_ToSMT_Term.DefineFun (_139_1128))
in (_139_1129)::[]))
in (
# 1234 "FStar.ToSMT.Encode.fst"
let quant = (fun vars body x -> (
# 1235 "FStar.ToSMT.Encode.fst"
let t1 = (let _139_1141 = (let _139_1140 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (x, _139_1140))
in (FStar_ToSMT_Term.mkApp _139_1141))
in (
# 1236 "FStar.ToSMT.Encode.fst"
let vname_decl = (let _139_1143 = (let _139_1142 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _139_1142, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_139_1143))
in (let _139_1149 = (let _139_1148 = (let _139_1147 = (let _139_1146 = (let _139_1145 = (let _139_1144 = (FStar_ToSMT_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _139_1144))
in (FStar_ToSMT_Term.mkForall _139_1145))
in (_139_1146, None))
in FStar_ToSMT_Term.Assume (_139_1147))
in (_139_1148)::[])
in (vname_decl)::_139_1149))))
in (
# 1239 "FStar.ToSMT.Encode.fst"
let def_or_quant = (fun vars body x -> if (FStar_ST.read FStar_Options.inline_arith) then begin
(deffun vars body x)
end else begin
(quant vars body x)
end)
in (
# 1243 "FStar.ToSMT.Encode.fst"
let axy = ((asym, FStar_ToSMT_Term.Type_sort))::((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (
# 1244 "FStar.ToSMT.Encode.fst"
let xy = ((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (
# 1245 "FStar.ToSMT.Encode.fst"
let qx = ((xsym, FStar_ToSMT_Term.Term_sort))::[]
in (
# 1246 "FStar.ToSMT.Encode.fst"
let prims = (let _139_1315 = (let _139_1164 = (let _139_1163 = (let _139_1162 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _139_1162))
in (def_or_quant axy _139_1163))
in (FStar_Absyn_Const.op_Eq, _139_1164))
in (let _139_1314 = (let _139_1313 = (let _139_1171 = (let _139_1170 = (let _139_1169 = (let _139_1168 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_ToSMT_Term.mkNot _139_1168))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _139_1169))
in (def_or_quant axy _139_1170))
in (FStar_Absyn_Const.op_notEq, _139_1171))
in (let _139_1312 = (let _139_1311 = (let _139_1180 = (let _139_1179 = (let _139_1178 = (let _139_1177 = (let _139_1176 = (FStar_ToSMT_Term.unboxInt x)
in (let _139_1175 = (FStar_ToSMT_Term.unboxInt y)
in (_139_1176, _139_1175)))
in (FStar_ToSMT_Term.mkLT _139_1177))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _139_1178))
in (def_or_quant xy _139_1179))
in (FStar_Absyn_Const.op_LT, _139_1180))
in (let _139_1310 = (let _139_1309 = (let _139_1189 = (let _139_1188 = (let _139_1187 = (let _139_1186 = (let _139_1185 = (FStar_ToSMT_Term.unboxInt x)
in (let _139_1184 = (FStar_ToSMT_Term.unboxInt y)
in (_139_1185, _139_1184)))
in (FStar_ToSMT_Term.mkLTE _139_1186))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _139_1187))
in (def_or_quant xy _139_1188))
in (FStar_Absyn_Const.op_LTE, _139_1189))
in (let _139_1308 = (let _139_1307 = (let _139_1198 = (let _139_1197 = (let _139_1196 = (let _139_1195 = (let _139_1194 = (FStar_ToSMT_Term.unboxInt x)
in (let _139_1193 = (FStar_ToSMT_Term.unboxInt y)
in (_139_1194, _139_1193)))
in (FStar_ToSMT_Term.mkGT _139_1195))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _139_1196))
in (def_or_quant xy _139_1197))
in (FStar_Absyn_Const.op_GT, _139_1198))
in (let _139_1306 = (let _139_1305 = (let _139_1207 = (let _139_1206 = (let _139_1205 = (let _139_1204 = (let _139_1203 = (FStar_ToSMT_Term.unboxInt x)
in (let _139_1202 = (FStar_ToSMT_Term.unboxInt y)
in (_139_1203, _139_1202)))
in (FStar_ToSMT_Term.mkGTE _139_1204))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _139_1205))
in (def_or_quant xy _139_1206))
in (FStar_Absyn_Const.op_GTE, _139_1207))
in (let _139_1304 = (let _139_1303 = (let _139_1216 = (let _139_1215 = (let _139_1214 = (let _139_1213 = (let _139_1212 = (FStar_ToSMT_Term.unboxInt x)
in (let _139_1211 = (FStar_ToSMT_Term.unboxInt y)
in (_139_1212, _139_1211)))
in (FStar_ToSMT_Term.mkSub _139_1213))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _139_1214))
in (def_or_quant xy _139_1215))
in (FStar_Absyn_Const.op_Subtraction, _139_1216))
in (let _139_1302 = (let _139_1301 = (let _139_1223 = (let _139_1222 = (let _139_1221 = (let _139_1220 = (FStar_ToSMT_Term.unboxInt x)
in (FStar_ToSMT_Term.mkMinus _139_1220))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _139_1221))
in (def_or_quant qx _139_1222))
in (FStar_Absyn_Const.op_Minus, _139_1223))
in (let _139_1300 = (let _139_1299 = (let _139_1232 = (let _139_1231 = (let _139_1230 = (let _139_1229 = (let _139_1228 = (FStar_ToSMT_Term.unboxInt x)
in (let _139_1227 = (FStar_ToSMT_Term.unboxInt y)
in (_139_1228, _139_1227)))
in (FStar_ToSMT_Term.mkAdd _139_1229))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _139_1230))
in (def_or_quant xy _139_1231))
in (FStar_Absyn_Const.op_Addition, _139_1232))
in (let _139_1298 = (let _139_1297 = (let _139_1241 = (let _139_1240 = (let _139_1239 = (let _139_1238 = (let _139_1237 = (FStar_ToSMT_Term.unboxInt x)
in (let _139_1236 = (FStar_ToSMT_Term.unboxInt y)
in (_139_1237, _139_1236)))
in (FStar_ToSMT_Term.mkMul _139_1238))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _139_1239))
in (def_or_quant xy _139_1240))
in (FStar_Absyn_Const.op_Multiply, _139_1241))
in (let _139_1296 = (let _139_1295 = (let _139_1250 = (let _139_1249 = (let _139_1248 = (let _139_1247 = (let _139_1246 = (FStar_ToSMT_Term.unboxInt x)
in (let _139_1245 = (FStar_ToSMT_Term.unboxInt y)
in (_139_1246, _139_1245)))
in (FStar_ToSMT_Term.mkDiv _139_1247))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _139_1248))
in (def_or_quant xy _139_1249))
in (FStar_Absyn_Const.op_Division, _139_1250))
in (let _139_1294 = (let _139_1293 = (let _139_1259 = (let _139_1258 = (let _139_1257 = (let _139_1256 = (let _139_1255 = (FStar_ToSMT_Term.unboxInt x)
in (let _139_1254 = (FStar_ToSMT_Term.unboxInt y)
in (_139_1255, _139_1254)))
in (FStar_ToSMT_Term.mkMod _139_1256))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _139_1257))
in (def_or_quant xy _139_1258))
in (FStar_Absyn_Const.op_Modulus, _139_1259))
in (let _139_1292 = (let _139_1291 = (let _139_1268 = (let _139_1267 = (let _139_1266 = (let _139_1265 = (let _139_1264 = (FStar_ToSMT_Term.unboxBool x)
in (let _139_1263 = (FStar_ToSMT_Term.unboxBool y)
in (_139_1264, _139_1263)))
in (FStar_ToSMT_Term.mkAnd _139_1265))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _139_1266))
in (def_or_quant xy _139_1267))
in (FStar_Absyn_Const.op_And, _139_1268))
in (let _139_1290 = (let _139_1289 = (let _139_1277 = (let _139_1276 = (let _139_1275 = (let _139_1274 = (let _139_1273 = (FStar_ToSMT_Term.unboxBool x)
in (let _139_1272 = (FStar_ToSMT_Term.unboxBool y)
in (_139_1273, _139_1272)))
in (FStar_ToSMT_Term.mkOr _139_1274))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _139_1275))
in (def_or_quant xy _139_1276))
in (FStar_Absyn_Const.op_Or, _139_1277))
in (let _139_1288 = (let _139_1287 = (let _139_1284 = (let _139_1283 = (let _139_1282 = (let _139_1281 = (FStar_ToSMT_Term.unboxBool x)
in (FStar_ToSMT_Term.mkNot _139_1281))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _139_1282))
in (def_or_quant qx _139_1283))
in (FStar_Absyn_Const.op_Negation, _139_1284))
in (_139_1287)::[])
in (_139_1289)::_139_1288))
in (_139_1291)::_139_1290))
in (_139_1293)::_139_1292))
in (_139_1295)::_139_1294))
in (_139_1297)::_139_1296))
in (_139_1299)::_139_1298))
in (_139_1301)::_139_1300))
in (_139_1303)::_139_1302))
in (_139_1305)::_139_1304))
in (_139_1307)::_139_1306))
in (_139_1309)::_139_1308))
in (_139_1311)::_139_1310))
in (_139_1313)::_139_1312))
in (_139_1315)::_139_1314))
in (
# 1263 "FStar.ToSMT.Encode.fst"
let mk = (fun l v -> (let _139_1347 = (FStar_All.pipe_right prims (FStar_List.filter (fun _50_2094 -> (match (_50_2094) with
| (l', _50_2093) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _139_1347 (FStar_List.collect (fun _50_2098 -> (match (_50_2098) with
| (_50_2096, b) -> begin
(b v)
end))))))
in (
# 1265 "FStar.ToSMT.Encode.fst"
let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _50_2104 -> (match (_50_2104) with
| (l', _50_2103) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))))
end))
end))
end))

# 1270 "FStar.ToSMT.Encode.fst"
let primitive_type_axioms : FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.decl Prims.list = (
# 1271 "FStar.ToSMT.Encode.fst"
let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (
# 1272 "FStar.ToSMT.Encode.fst"
let x = (FStar_ToSMT_Term.mkFreeV xx)
in (
# 1274 "FStar.ToSMT.Encode.fst"
let yy = ("y", FStar_ToSMT_Term.Term_sort)
in (
# 1275 "FStar.ToSMT.Encode.fst"
let y = (FStar_ToSMT_Term.mkFreeV yy)
in (
# 1277 "FStar.ToSMT.Encode.fst"
let mk_unit = (fun _50_2110 tt -> (
# 1278 "FStar.ToSMT.Encode.fst"
let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let _139_1379 = (let _139_1370 = (let _139_1369 = (FStar_ToSMT_Term.mk_HasType FStar_ToSMT_Term.mk_Term_unit tt)
in (_139_1369, Some ("unit typing")))
in FStar_ToSMT_Term.Assume (_139_1370))
in (let _139_1378 = (let _139_1377 = (let _139_1376 = (let _139_1375 = (let _139_1374 = (let _139_1373 = (let _139_1372 = (let _139_1371 = (FStar_ToSMT_Term.mkEq (x, FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _139_1371))
in (FStar_ToSMT_Term.mkImp _139_1372))
in (((typing_pred)::[])::[], (xx)::[], _139_1373))
in (mkForall_fuel _139_1374))
in (_139_1375, Some ("unit inversion")))
in FStar_ToSMT_Term.Assume (_139_1376))
in (_139_1377)::[])
in (_139_1379)::_139_1378))))
in (
# 1281 "FStar.ToSMT.Encode.fst"
let mk_bool = (fun _50_2115 tt -> (
# 1282 "FStar.ToSMT.Encode.fst"
let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (
# 1283 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Bool_sort)
in (
# 1284 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _139_1400 = (let _139_1389 = (let _139_1388 = (let _139_1387 = (let _139_1386 = (let _139_1385 = (let _139_1384 = (FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _139_1384))
in (FStar_ToSMT_Term.mkImp _139_1385))
in (((typing_pred)::[])::[], (xx)::[], _139_1386))
in (mkForall_fuel _139_1387))
in (_139_1388, Some ("bool inversion")))
in FStar_ToSMT_Term.Assume (_139_1389))
in (let _139_1399 = (let _139_1398 = (let _139_1397 = (let _139_1396 = (let _139_1395 = (let _139_1394 = (let _139_1391 = (let _139_1390 = (FStar_ToSMT_Term.boxBool b)
in (_139_1390)::[])
in (_139_1391)::[])
in (let _139_1393 = (let _139_1392 = (FStar_ToSMT_Term.boxBool b)
in (FStar_ToSMT_Term.mk_HasType _139_1392 tt))
in (_139_1394, (bb)::[], _139_1393)))
in (FStar_ToSMT_Term.mkForall _139_1395))
in (_139_1396, Some ("bool typing")))
in FStar_ToSMT_Term.Assume (_139_1397))
in (_139_1398)::[])
in (_139_1400)::_139_1399))))))
in (
# 1287 "FStar.ToSMT.Encode.fst"
let mk_int = (fun _50_2122 tt -> (
# 1288 "FStar.ToSMT.Encode.fst"
let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (
# 1289 "FStar.ToSMT.Encode.fst"
let typing_pred_y = (FStar_ToSMT_Term.mk_HasType y tt)
in (
# 1290 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Int_sort)
in (
# 1291 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1292 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Int_sort)
in (
# 1293 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1294 "FStar.ToSMT.Encode.fst"
let precedes = (let _139_1412 = (let _139_1411 = (let _139_1410 = (let _139_1409 = (let _139_1408 = (let _139_1407 = (FStar_ToSMT_Term.boxInt a)
in (let _139_1406 = (let _139_1405 = (FStar_ToSMT_Term.boxInt b)
in (_139_1405)::[])
in (_139_1407)::_139_1406))
in (tt)::_139_1408)
in (tt)::_139_1409)
in ("Prims.Precedes", _139_1410))
in (FStar_ToSMT_Term.mkApp _139_1411))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _139_1412))
in (
# 1295 "FStar.ToSMT.Encode.fst"
let precedes_y_x = (let _139_1413 = (FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _139_1413))
in (let _139_1455 = (let _139_1419 = (let _139_1418 = (let _139_1417 = (let _139_1416 = (let _139_1415 = (let _139_1414 = (FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _139_1414))
in (FStar_ToSMT_Term.mkImp _139_1415))
in (((typing_pred)::[])::[], (xx)::[], _139_1416))
in (mkForall_fuel _139_1417))
in (_139_1418, Some ("int inversion")))
in FStar_ToSMT_Term.Assume (_139_1419))
in (let _139_1454 = (let _139_1453 = (let _139_1427 = (let _139_1426 = (let _139_1425 = (let _139_1424 = (let _139_1421 = (let _139_1420 = (FStar_ToSMT_Term.boxInt b)
in (_139_1420)::[])
in (_139_1421)::[])
in (let _139_1423 = (let _139_1422 = (FStar_ToSMT_Term.boxInt b)
in (FStar_ToSMT_Term.mk_HasType _139_1422 tt))
in (_139_1424, (bb)::[], _139_1423)))
in (FStar_ToSMT_Term.mkForall _139_1425))
in (_139_1426, Some ("int typing")))
in FStar_ToSMT_Term.Assume (_139_1427))
in (let _139_1452 = (let _139_1451 = (let _139_1450 = (let _139_1449 = (let _139_1448 = (let _139_1447 = (let _139_1446 = (let _139_1445 = (let _139_1444 = (let _139_1443 = (let _139_1442 = (let _139_1441 = (let _139_1430 = (let _139_1429 = (FStar_ToSMT_Term.unboxInt x)
in (let _139_1428 = (FStar_ToSMT_Term.mkInteger' 0)
in (_139_1429, _139_1428)))
in (FStar_ToSMT_Term.mkGT _139_1430))
in (let _139_1440 = (let _139_1439 = (let _139_1433 = (let _139_1432 = (FStar_ToSMT_Term.unboxInt y)
in (let _139_1431 = (FStar_ToSMT_Term.mkInteger' 0)
in (_139_1432, _139_1431)))
in (FStar_ToSMT_Term.mkGTE _139_1433))
in (let _139_1438 = (let _139_1437 = (let _139_1436 = (let _139_1435 = (FStar_ToSMT_Term.unboxInt y)
in (let _139_1434 = (FStar_ToSMT_Term.unboxInt x)
in (_139_1435, _139_1434)))
in (FStar_ToSMT_Term.mkLT _139_1436))
in (_139_1437)::[])
in (_139_1439)::_139_1438))
in (_139_1441)::_139_1440))
in (typing_pred_y)::_139_1442)
in (typing_pred)::_139_1443)
in (FStar_ToSMT_Term.mk_and_l _139_1444))
in (_139_1445, precedes_y_x))
in (FStar_ToSMT_Term.mkImp _139_1446))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _139_1447))
in (mkForall_fuel _139_1448))
in (_139_1449, Some ("well-founded ordering on nat (alt)")))
in FStar_ToSMT_Term.Assume (_139_1450))
in (_139_1451)::[])
in (_139_1453)::_139_1452))
in (_139_1455)::_139_1454)))))))))))
in (
# 1307 "FStar.ToSMT.Encode.fst"
let mk_int_alias = (fun _50_2134 tt -> (let _139_1464 = (let _139_1463 = (let _139_1462 = (let _139_1461 = (let _139_1460 = (FStar_ToSMT_Term.mkApp (FStar_Absyn_Const.int_lid.FStar_Ident.str, []))
in (tt, _139_1460))
in (FStar_ToSMT_Term.mkEq _139_1461))
in (_139_1462, Some ("mapping to int; for now")))
in FStar_ToSMT_Term.Assume (_139_1463))
in (_139_1464)::[]))
in (
# 1309 "FStar.ToSMT.Encode.fst"
let mk_str = (fun _50_2138 tt -> (
# 1310 "FStar.ToSMT.Encode.fst"
let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (
# 1311 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.String_sort)
in (
# 1312 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _139_1485 = (let _139_1474 = (let _139_1473 = (let _139_1472 = (let _139_1471 = (let _139_1470 = (let _139_1469 = (FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _139_1469))
in (FStar_ToSMT_Term.mkImp _139_1470))
in (((typing_pred)::[])::[], (xx)::[], _139_1471))
in (mkForall_fuel _139_1472))
in (_139_1473, Some ("string inversion")))
in FStar_ToSMT_Term.Assume (_139_1474))
in (let _139_1484 = (let _139_1483 = (let _139_1482 = (let _139_1481 = (let _139_1480 = (let _139_1479 = (let _139_1476 = (let _139_1475 = (FStar_ToSMT_Term.boxString b)
in (_139_1475)::[])
in (_139_1476)::[])
in (let _139_1478 = (let _139_1477 = (FStar_ToSMT_Term.boxString b)
in (FStar_ToSMT_Term.mk_HasType _139_1477 tt))
in (_139_1479, (bb)::[], _139_1478)))
in (FStar_ToSMT_Term.mkForall _139_1480))
in (_139_1481, Some ("string typing")))
in FStar_ToSMT_Term.Assume (_139_1482))
in (_139_1483)::[])
in (_139_1485)::_139_1484))))))
in (
# 1315 "FStar.ToSMT.Encode.fst"
let mk_ref = (fun reft_name _50_2146 -> (
# 1316 "FStar.ToSMT.Encode.fst"
let r = ("r", FStar_ToSMT_Term.Ref_sort)
in (
# 1317 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (
# 1318 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (
# 1319 "FStar.ToSMT.Encode.fst"
let refa = (let _139_1492 = (let _139_1491 = (let _139_1490 = (FStar_ToSMT_Term.mkFreeV aa)
in (_139_1490)::[])
in (reft_name, _139_1491))
in (FStar_ToSMT_Term.mkApp _139_1492))
in (
# 1320 "FStar.ToSMT.Encode.fst"
let refb = (let _139_1495 = (let _139_1494 = (let _139_1493 = (FStar_ToSMT_Term.mkFreeV bb)
in (_139_1493)::[])
in (reft_name, _139_1494))
in (FStar_ToSMT_Term.mkApp _139_1495))
in (
# 1321 "FStar.ToSMT.Encode.fst"
let typing_pred = (FStar_ToSMT_Term.mk_HasType x refa)
in (
# 1322 "FStar.ToSMT.Encode.fst"
let typing_pred_b = (FStar_ToSMT_Term.mk_HasType x refb)
in (let _139_1514 = (let _139_1501 = (let _139_1500 = (let _139_1499 = (let _139_1498 = (let _139_1497 = (let _139_1496 = (FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _139_1496))
in (FStar_ToSMT_Term.mkImp _139_1497))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _139_1498))
in (mkForall_fuel _139_1499))
in (_139_1500, Some ("ref inversion")))
in FStar_ToSMT_Term.Assume (_139_1501))
in (let _139_1513 = (let _139_1512 = (let _139_1511 = (let _139_1510 = (let _139_1509 = (let _139_1508 = (let _139_1507 = (let _139_1506 = (FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _139_1505 = (let _139_1504 = (let _139_1503 = (FStar_ToSMT_Term.mkFreeV aa)
in (let _139_1502 = (FStar_ToSMT_Term.mkFreeV bb)
in (_139_1503, _139_1502)))
in (FStar_ToSMT_Term.mkEq _139_1504))
in (_139_1506, _139_1505)))
in (FStar_ToSMT_Term.mkImp _139_1507))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _139_1508))
in (mkForall_fuel' 2 _139_1509))
in (_139_1510, Some ("ref typing is injective")))
in FStar_ToSMT_Term.Assume (_139_1511))
in (_139_1512)::[])
in (_139_1514)::_139_1513))))))))))
in (
# 1326 "FStar.ToSMT.Encode.fst"
let mk_false_interp = (fun _50_2156 false_tm -> (
# 1327 "FStar.ToSMT.Encode.fst"
let valid = (FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _139_1521 = (let _139_1520 = (let _139_1519 = (FStar_ToSMT_Term.mkIff (FStar_ToSMT_Term.mkFalse, valid))
in (_139_1519, Some ("False interpretation")))
in FStar_ToSMT_Term.Assume (_139_1520))
in (_139_1521)::[])))
in (
# 1329 "FStar.ToSMT.Encode.fst"
let mk_and_interp = (fun conj _50_2162 -> (
# 1330 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (
# 1331 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (
# 1332 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1333 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1334 "FStar.ToSMT.Encode.fst"
let valid = (let _139_1528 = (let _139_1527 = (let _139_1526 = (FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_139_1526)::[])
in ("Valid", _139_1527))
in (FStar_ToSMT_Term.mkApp _139_1528))
in (
# 1335 "FStar.ToSMT.Encode.fst"
let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (
# 1336 "FStar.ToSMT.Encode.fst"
let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _139_1535 = (let _139_1534 = (let _139_1533 = (let _139_1532 = (let _139_1531 = (let _139_1530 = (let _139_1529 = (FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_139_1529, valid))
in (FStar_ToSMT_Term.mkIff _139_1530))
in (((valid)::[])::[], (aa)::(bb)::[], _139_1531))
in (FStar_ToSMT_Term.mkForall _139_1532))
in (_139_1533, Some ("/\\ interpretation")))
in FStar_ToSMT_Term.Assume (_139_1534))
in (_139_1535)::[])))))))))
in (
# 1338 "FStar.ToSMT.Encode.fst"
let mk_or_interp = (fun disj _50_2173 -> (
# 1339 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (
# 1340 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (
# 1341 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1342 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1343 "FStar.ToSMT.Encode.fst"
let valid = (let _139_1542 = (let _139_1541 = (let _139_1540 = (FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_139_1540)::[])
in ("Valid", _139_1541))
in (FStar_ToSMT_Term.mkApp _139_1542))
in (
# 1344 "FStar.ToSMT.Encode.fst"
let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (
# 1345 "FStar.ToSMT.Encode.fst"
let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _139_1549 = (let _139_1548 = (let _139_1547 = (let _139_1546 = (let _139_1545 = (let _139_1544 = (let _139_1543 = (FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_139_1543, valid))
in (FStar_ToSMT_Term.mkIff _139_1544))
in (((valid)::[])::[], (aa)::(bb)::[], _139_1545))
in (FStar_ToSMT_Term.mkForall _139_1546))
in (_139_1547, Some ("\\/ interpretation")))
in FStar_ToSMT_Term.Assume (_139_1548))
in (_139_1549)::[])))))))))
in (
# 1347 "FStar.ToSMT.Encode.fst"
let mk_eq2_interp = (fun eq2 tt -> (
# 1348 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (
# 1349 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (
# 1350 "FStar.ToSMT.Encode.fst"
let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (
# 1351 "FStar.ToSMT.Encode.fst"
let yy = ("y", FStar_ToSMT_Term.Term_sort)
in (
# 1352 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1353 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1354 "FStar.ToSMT.Encode.fst"
let x = (FStar_ToSMT_Term.mkFreeV xx)
in (
# 1355 "FStar.ToSMT.Encode.fst"
let y = (FStar_ToSMT_Term.mkFreeV yy)
in (
# 1356 "FStar.ToSMT.Encode.fst"
let valid = (let _139_1556 = (let _139_1555 = (let _139_1554 = (FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_139_1554)::[])
in ("Valid", _139_1555))
in (FStar_ToSMT_Term.mkApp _139_1556))
in (let _139_1563 = (let _139_1562 = (let _139_1561 = (let _139_1560 = (let _139_1559 = (let _139_1558 = (let _139_1557 = (FStar_ToSMT_Term.mkEq (x, y))
in (_139_1557, valid))
in (FStar_ToSMT_Term.mkIff _139_1558))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _139_1559))
in (FStar_ToSMT_Term.mkForall _139_1560))
in (_139_1561, Some ("Eq2 interpretation")))
in FStar_ToSMT_Term.Assume (_139_1562))
in (_139_1563)::[])))))))))))
in (
# 1358 "FStar.ToSMT.Encode.fst"
let mk_imp_interp = (fun imp tt -> (
# 1359 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (
# 1360 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (
# 1361 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1362 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1363 "FStar.ToSMT.Encode.fst"
let valid = (let _139_1570 = (let _139_1569 = (let _139_1568 = (FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_139_1568)::[])
in ("Valid", _139_1569))
in (FStar_ToSMT_Term.mkApp _139_1570))
in (
# 1364 "FStar.ToSMT.Encode.fst"
let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (
# 1365 "FStar.ToSMT.Encode.fst"
let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _139_1577 = (let _139_1576 = (let _139_1575 = (let _139_1574 = (let _139_1573 = (let _139_1572 = (let _139_1571 = (FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_139_1571, valid))
in (FStar_ToSMT_Term.mkIff _139_1572))
in (((valid)::[])::[], (aa)::(bb)::[], _139_1573))
in (FStar_ToSMT_Term.mkForall _139_1574))
in (_139_1575, Some ("==> interpretation")))
in FStar_ToSMT_Term.Assume (_139_1576))
in (_139_1577)::[])))))))))
in (
# 1367 "FStar.ToSMT.Encode.fst"
let mk_iff_interp = (fun iff tt -> (
# 1368 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (
# 1369 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (
# 1370 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1371 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1372 "FStar.ToSMT.Encode.fst"
let valid = (let _139_1584 = (let _139_1583 = (let _139_1582 = (FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_139_1582)::[])
in ("Valid", _139_1583))
in (FStar_ToSMT_Term.mkApp _139_1584))
in (
# 1373 "FStar.ToSMT.Encode.fst"
let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (
# 1374 "FStar.ToSMT.Encode.fst"
let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _139_1591 = (let _139_1590 = (let _139_1589 = (let _139_1588 = (let _139_1587 = (let _139_1586 = (let _139_1585 = (FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_139_1585, valid))
in (FStar_ToSMT_Term.mkIff _139_1586))
in (((valid)::[])::[], (aa)::(bb)::[], _139_1587))
in (FStar_ToSMT_Term.mkForall _139_1588))
in (_139_1589, Some ("<==> interpretation")))
in FStar_ToSMT_Term.Assume (_139_1590))
in (_139_1591)::[])))))))))
in (
# 1376 "FStar.ToSMT.Encode.fst"
let mk_forall_interp = (fun for_all tt -> (
# 1377 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (
# 1378 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (
# 1379 "FStar.ToSMT.Encode.fst"
let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (
# 1380 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1381 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1382 "FStar.ToSMT.Encode.fst"
let x = (FStar_ToSMT_Term.mkFreeV xx)
in (
# 1383 "FStar.ToSMT.Encode.fst"
let valid = (let _139_1598 = (let _139_1597 = (let _139_1596 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_139_1596)::[])
in ("Valid", _139_1597))
in (FStar_ToSMT_Term.mkApp _139_1598))
in (
# 1384 "FStar.ToSMT.Encode.fst"
let valid_b_x = (let _139_1601 = (let _139_1600 = (let _139_1599 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_139_1599)::[])
in ("Valid", _139_1600))
in (FStar_ToSMT_Term.mkApp _139_1601))
in (let _139_1615 = (let _139_1614 = (let _139_1613 = (let _139_1612 = (let _139_1611 = (let _139_1610 = (let _139_1609 = (let _139_1608 = (let _139_1607 = (let _139_1603 = (let _139_1602 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_139_1602)::[])
in (_139_1603)::[])
in (let _139_1606 = (let _139_1605 = (let _139_1604 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_139_1604, valid_b_x))
in (FStar_ToSMT_Term.mkImp _139_1605))
in (_139_1607, (xx)::[], _139_1606)))
in (FStar_ToSMT_Term.mkForall _139_1608))
in (_139_1609, valid))
in (FStar_ToSMT_Term.mkIff _139_1610))
in (((valid)::[])::[], (aa)::(bb)::[], _139_1611))
in (FStar_ToSMT_Term.mkForall _139_1612))
in (_139_1613, Some ("forall interpretation")))
in FStar_ToSMT_Term.Assume (_139_1614))
in (_139_1615)::[]))))))))))
in (
# 1386 "FStar.ToSMT.Encode.fst"
let mk_exists_interp = (fun for_all tt -> (
# 1387 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (
# 1388 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (
# 1389 "FStar.ToSMT.Encode.fst"
let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (
# 1390 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1391 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1392 "FStar.ToSMT.Encode.fst"
let x = (FStar_ToSMT_Term.mkFreeV xx)
in (
# 1393 "FStar.ToSMT.Encode.fst"
let valid = (let _139_1622 = (let _139_1621 = (let _139_1620 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_139_1620)::[])
in ("Valid", _139_1621))
in (FStar_ToSMT_Term.mkApp _139_1622))
in (
# 1394 "FStar.ToSMT.Encode.fst"
let valid_b_x = (let _139_1625 = (let _139_1624 = (let _139_1623 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_139_1623)::[])
in ("Valid", _139_1624))
in (FStar_ToSMT_Term.mkApp _139_1625))
in (let _139_1639 = (let _139_1638 = (let _139_1637 = (let _139_1636 = (let _139_1635 = (let _139_1634 = (let _139_1633 = (let _139_1632 = (let _139_1631 = (let _139_1627 = (let _139_1626 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_139_1626)::[])
in (_139_1627)::[])
in (let _139_1630 = (let _139_1629 = (let _139_1628 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_139_1628, valid_b_x))
in (FStar_ToSMT_Term.mkImp _139_1629))
in (_139_1631, (xx)::[], _139_1630)))
in (FStar_ToSMT_Term.mkExists _139_1632))
in (_139_1633, valid))
in (FStar_ToSMT_Term.mkIff _139_1634))
in (((valid)::[])::[], (aa)::(bb)::[], _139_1635))
in (FStar_ToSMT_Term.mkForall _139_1636))
in (_139_1637, Some ("exists interpretation")))
in FStar_ToSMT_Term.Assume (_139_1638))
in (_139_1639)::[]))))))))))
in (
# 1396 "FStar.ToSMT.Encode.fst"
let mk_foralltyp_interp = (fun for_all tt -> (
# 1397 "FStar.ToSMT.Encode.fst"
let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (
# 1398 "FStar.ToSMT.Encode.fst"
let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (
# 1399 "FStar.ToSMT.Encode.fst"
let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (
# 1400 "FStar.ToSMT.Encode.fst"
let k = (FStar_ToSMT_Term.mkFreeV kk)
in (
# 1401 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1402 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1403 "FStar.ToSMT.Encode.fst"
let valid = (let _139_1646 = (let _139_1645 = (let _139_1644 = (FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_139_1644)::[])
in ("Valid", _139_1645))
in (FStar_ToSMT_Term.mkApp _139_1646))
in (
# 1404 "FStar.ToSMT.Encode.fst"
let valid_a_b = (let _139_1649 = (let _139_1648 = (let _139_1647 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_139_1647)::[])
in ("Valid", _139_1648))
in (FStar_ToSMT_Term.mkApp _139_1649))
in (let _139_1663 = (let _139_1662 = (let _139_1661 = (let _139_1660 = (let _139_1659 = (let _139_1658 = (let _139_1657 = (let _139_1656 = (let _139_1655 = (let _139_1651 = (let _139_1650 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_139_1650)::[])
in (_139_1651)::[])
in (let _139_1654 = (let _139_1653 = (let _139_1652 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_139_1652, valid_a_b))
in (FStar_ToSMT_Term.mkImp _139_1653))
in (_139_1655, (bb)::[], _139_1654)))
in (FStar_ToSMT_Term.mkForall _139_1656))
in (_139_1657, valid))
in (FStar_ToSMT_Term.mkIff _139_1658))
in (((valid)::[])::[], (kk)::(aa)::[], _139_1659))
in (FStar_ToSMT_Term.mkForall _139_1660))
in (_139_1661, Some ("ForallTyp interpretation")))
in FStar_ToSMT_Term.Assume (_139_1662))
in (_139_1663)::[]))))))))))
in (
# 1406 "FStar.ToSMT.Encode.fst"
let mk_existstyp_interp = (fun for_some tt -> (
# 1407 "FStar.ToSMT.Encode.fst"
let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (
# 1408 "FStar.ToSMT.Encode.fst"
let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (
# 1409 "FStar.ToSMT.Encode.fst"
let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (
# 1410 "FStar.ToSMT.Encode.fst"
let k = (FStar_ToSMT_Term.mkFreeV kk)
in (
# 1411 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1412 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1413 "FStar.ToSMT.Encode.fst"
let valid = (let _139_1670 = (let _139_1669 = (let _139_1668 = (FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_139_1668)::[])
in ("Valid", _139_1669))
in (FStar_ToSMT_Term.mkApp _139_1670))
in (
# 1414 "FStar.ToSMT.Encode.fst"
let valid_a_b = (let _139_1673 = (let _139_1672 = (let _139_1671 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_139_1671)::[])
in ("Valid", _139_1672))
in (FStar_ToSMT_Term.mkApp _139_1673))
in (let _139_1687 = (let _139_1686 = (let _139_1685 = (let _139_1684 = (let _139_1683 = (let _139_1682 = (let _139_1681 = (let _139_1680 = (let _139_1679 = (let _139_1675 = (let _139_1674 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_139_1674)::[])
in (_139_1675)::[])
in (let _139_1678 = (let _139_1677 = (let _139_1676 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_139_1676, valid_a_b))
in (FStar_ToSMT_Term.mkImp _139_1677))
in (_139_1679, (bb)::[], _139_1678)))
in (FStar_ToSMT_Term.mkExists _139_1680))
in (_139_1681, valid))
in (FStar_ToSMT_Term.mkIff _139_1682))
in (((valid)::[])::[], (kk)::(aa)::[], _139_1683))
in (FStar_ToSMT_Term.mkForall _139_1684))
in (_139_1685, Some ("ExistsTyp interpretation")))
in FStar_ToSMT_Term.Assume (_139_1686))
in (_139_1687)::[]))))))))))
in (
# 1417 "FStar.ToSMT.Encode.fst"
let prims = ((FStar_Absyn_Const.unit_lid, mk_unit))::((FStar_Absyn_Const.bool_lid, mk_bool))::((FStar_Absyn_Const.int_lid, mk_int))::((FStar_Absyn_Const.string_lid, mk_str))::((FStar_Absyn_Const.ref_lid, mk_ref))::((FStar_Absyn_Const.false_lid, mk_false_interp))::((FStar_Absyn_Const.and_lid, mk_and_interp))::((FStar_Absyn_Const.or_lid, mk_or_interp))::((FStar_Absyn_Const.eq2_lid, mk_eq2_interp))::((FStar_Absyn_Const.imp_lid, mk_imp_interp))::((FStar_Absyn_Const.iff_lid, mk_iff_interp))::((FStar_Absyn_Const.forall_lid, mk_forall_interp))::((FStar_Absyn_Const.exists_lid, mk_exists_interp))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _50_2266 -> (match (_50_2266) with
| (l, _50_2265) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_50_2269, f) -> begin
(f s tt)
end)))))))))))))))))))))))

# 1440 "FStar.ToSMT.Encode.fst"
let rec encode_sigelt : env_t  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_ToSMT_Term.decls_t * env_t) = (fun env se -> (
# 1441 "FStar.ToSMT.Encode.fst"
let _50_2275 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _139_1818 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _139_1818))
end else begin
()
end
in (
# 1444 "FStar.ToSMT.Encode.fst"
let nm = (match ((FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (
# 1447 "FStar.ToSMT.Encode.fst"
let _50_2283 = (encode_sigelt' env se)
in (match (_50_2283) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _139_1821 = (let _139_1820 = (let _139_1819 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_ToSMT_Term.Caption (_139_1819))
in (_139_1820)::[])
in (_139_1821, e))
end
| _50_2286 -> begin
(let _139_1828 = (let _139_1827 = (let _139_1823 = (let _139_1822 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_139_1822))
in (_139_1823)::g)
in (let _139_1826 = (let _139_1825 = (let _139_1824 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_139_1824))
in (_139_1825)::[])
in (FStar_List.append _139_1827 _139_1826)))
in (_139_1828, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_ToSMT_Term.decls_t * env_t) = (fun env se -> (
# 1453 "FStar.ToSMT.Encode.fst"
let should_skip = (fun l -> ((((FStar_Util.starts_with l.FStar_Ident.str "Prims.pure_") || (FStar_Util.starts_with l.FStar_Ident.str "Prims.ex_")) || (FStar_Util.starts_with l.FStar_Ident.str "Prims.st_")) || (FStar_Util.starts_with l.FStar_Ident.str "Prims.all_")))
in (
# 1460 "FStar.ToSMT.Encode.fst"
let encode_top_level_val = (fun env lid t quals -> (
# 1461 "FStar.ToSMT.Encode.fst"
let tt = (whnf env t)
in (
# 1462 "FStar.ToSMT.Encode.fst"
let _50_2299 = (encode_free_var env lid t tt quals)
in (match (_50_2299) with
| (decls, env) -> begin
if (FStar_Absyn_Util.is_smt_lemma t) then begin
(let _139_1842 = (let _139_1841 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _139_1841))
in (_139_1842, env))
end else begin
(decls, env)
end
end))))
in (
# 1468 "FStar.ToSMT.Encode.fst"
let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _50_2306 lb -> (match (_50_2306) with
| (decls, env) -> begin
(
# 1470 "FStar.ToSMT.Encode.fst"
let _50_2310 = (let _139_1851 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (encode_top_level_val env _139_1851 lb.FStar_Absyn_Syntax.lbtyp quals))
in (match (_50_2310) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_50_2312, _50_2314, _50_2316, _50_2318, FStar_Absyn_Syntax.Effect::[], _50_2322) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _50_2327, _50_2329, _50_2331, _50_2333, _50_2335) when (should_skip lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _50_2340, _50_2342, _50_2344, _50_2346, _50_2348) when (FStar_Ident.lid_equals lid FStar_Absyn_Const.b2t_lid) -> begin
(
# 1479 "FStar.ToSMT.Encode.fst"
let _50_2354 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_50_2354) with
| (tname, ttok, env) -> begin
(
# 1480 "FStar.ToSMT.Encode.fst"
let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (
# 1481 "FStar.ToSMT.Encode.fst"
let x = (FStar_ToSMT_Term.mkFreeV xx)
in (
# 1482 "FStar.ToSMT.Encode.fst"
let valid_b2t_x = (let _139_1854 = (let _139_1853 = (let _139_1852 = (FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (_139_1852)::[])
in ("Valid", _139_1853))
in (FStar_ToSMT_Term.mkApp _139_1854))
in (
# 1483 "FStar.ToSMT.Encode.fst"
let decls = (let _139_1862 = (let _139_1861 = (let _139_1860 = (let _139_1859 = (let _139_1858 = (let _139_1857 = (let _139_1856 = (let _139_1855 = (FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _139_1855))
in (FStar_ToSMT_Term.mkEq _139_1856))
in (((valid_b2t_x)::[])::[], (xx)::[], _139_1857))
in (FStar_ToSMT_Term.mkForall _139_1858))
in (_139_1859, Some ("b2t def")))
in FStar_ToSMT_Term.Assume (_139_1860))
in (_139_1861)::[])
in (FStar_ToSMT_Term.DeclFun ((tname, (FStar_ToSMT_Term.Term_sort)::[], FStar_ToSMT_Term.Type_sort, None)))::_139_1862)
in (decls, env)))))
end))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _50_2362, t, tags, _50_2366) -> begin
(
# 1490 "FStar.ToSMT.Encode.fst"
let _50_2372 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_50_2372) with
| (tname, ttok, env) -> begin
(
# 1491 "FStar.ToSMT.Encode.fst"
let _50_2381 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (tps', body) -> begin
((FStar_List.append tps tps'), body)
end
| _50_2378 -> begin
(tps, t)
end)
in (match (_50_2381) with
| (tps, t) -> begin
(
# 1494 "FStar.ToSMT.Encode.fst"
let _50_2388 = (encode_binders None tps env)
in (match (_50_2388) with
| (vars, guards, env', binder_decls, _50_2387) -> begin
(
# 1495 "FStar.ToSMT.Encode.fst"
let tok_app = (let _139_1863 = (FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _139_1863 vars))
in (
# 1496 "FStar.ToSMT.Encode.fst"
let tok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, None))
in (
# 1497 "FStar.ToSMT.Encode.fst"
let app = (let _139_1865 = (let _139_1864 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _139_1864))
in (FStar_ToSMT_Term.mkApp _139_1865))
in (
# 1498 "FStar.ToSMT.Encode.fst"
let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _50_2394 -> begin
(let _139_1867 = (let _139_1866 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _139_1866))
in (_139_1867)::[])
end)
in (
# 1501 "FStar.ToSMT.Encode.fst"
let decls = (let _139_1878 = (let _139_1871 = (let _139_1870 = (let _139_1869 = (let _139_1868 = (FStar_List.map Prims.snd vars)
in (tname, _139_1868, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_139_1869))
in (_139_1870)::(tok_decl)::[])
in (FStar_List.append _139_1871 fresh_tok))
in (let _139_1877 = (let _139_1876 = (let _139_1875 = (let _139_1874 = (let _139_1873 = (let _139_1872 = (FStar_ToSMT_Term.mkEq (tok_app, app))
in (((tok_app)::[])::[], vars, _139_1872))
in (FStar_ToSMT_Term.mkForall _139_1873))
in (_139_1874, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_139_1875))
in (_139_1876)::[])
in (FStar_List.append _139_1878 _139_1877)))
in (
# 1505 "FStar.ToSMT.Encode.fst"
let t = if (FStar_All.pipe_right tags (FStar_List.contains FStar_Absyn_Syntax.Opaque)) then begin
(FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
end else begin
(whnf env t)
end
in (
# 1508 "FStar.ToSMT.Encode.fst"
let _50_2406 = if (FStar_All.pipe_right tags (FStar_Util.for_some (fun _50_18 -> (match (_50_18) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _50_2401 -> begin
false
end)))) then begin
(let _139_1881 = (FStar_ToSMT_Term.mk_Valid app)
in (let _139_1880 = (encode_formula t env')
in (_139_1881, _139_1880)))
end else begin
(let _139_1882 = (encode_typ_term t env')
in (app, _139_1882))
end
in (match (_50_2406) with
| (def, (body, decls1)) -> begin
(
# 1512 "FStar.ToSMT.Encode.fst"
let abbrev_def = (let _139_1889 = (let _139_1888 = (let _139_1887 = (let _139_1886 = (let _139_1885 = (let _139_1884 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _139_1883 = (FStar_ToSMT_Term.mkEq (def, body))
in (_139_1884, _139_1883)))
in (FStar_ToSMT_Term.mkImp _139_1885))
in (((def)::[])::[], vars, _139_1886))
in (FStar_ToSMT_Term.mkForall _139_1887))
in (_139_1888, Some ("abbrev. elimination")))
in FStar_ToSMT_Term.Assume (_139_1889))
in (
# 1513 "FStar.ToSMT.Encode.fst"
let kindingAx = (
# 1514 "FStar.ToSMT.Encode.fst"
let _50_2410 = (let _139_1890 = (FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _139_1890 env' app))
in (match (_50_2410) with
| (k, decls) -> begin
(let _139_1898 = (let _139_1897 = (let _139_1896 = (let _139_1895 = (let _139_1894 = (let _139_1893 = (let _139_1892 = (let _139_1891 = (FStar_ToSMT_Term.mk_and_l guards)
in (_139_1891, k))
in (FStar_ToSMT_Term.mkImp _139_1892))
in (((app)::[])::[], vars, _139_1893))
in (FStar_ToSMT_Term.mkForall _139_1894))
in (_139_1895, Some ("abbrev. kinding")))
in FStar_ToSMT_Term.Assume (_139_1896))
in (_139_1897)::[])
in (FStar_List.append decls _139_1898))
end))
in (
# 1516 "FStar.ToSMT.Encode.fst"
let g = (let _139_1899 = (primitive_type_axioms lid tname app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _139_1899))
in (g, env))))
end))))))))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _50_2417) -> begin
if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || env.tcenv.FStar_Tc_Env.is_iface) then begin
(encode_top_level_val env lid t quals)
end else begin
([], env)
end
end
| FStar_Absyn_Syntax.Sig_assume (l, f, _50_2423, _50_2425) -> begin
(
# 1526 "FStar.ToSMT.Encode.fst"
let _50_2430 = (encode_formula f env)
in (match (_50_2430) with
| (f, decls) -> begin
(
# 1527 "FStar.ToSMT.Encode.fst"
let g = (let _139_1904 = (let _139_1903 = (let _139_1902 = (let _139_1901 = (let _139_1900 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "Assumption: %s" _139_1900))
in Some (_139_1901))
in (f, _139_1902))
in FStar_ToSMT_Term.Assume (_139_1903))
in (_139_1904)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _50_2436, datas, quals, _50_2440) when (FStar_Ident.lid_equals t FStar_Absyn_Const.precedes_lid) -> begin
(
# 1531 "FStar.ToSMT.Encode.fst"
let _50_2446 = (new_typ_constant_and_tok_from_lid env t)
in (match (_50_2446) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, _50_2449, _50_2451, _50_2453, _50_2455, _50_2457, _50_2459) when ((FStar_Ident.lid_equals t FStar_Absyn_Const.char_lid) || (FStar_Ident.lid_equals t FStar_Absyn_Const.uint8_lid)) -> begin
(
# 1535 "FStar.ToSMT.Encode.fst"
let tname = t.FStar_Ident.str
in (
# 1536 "FStar.ToSMT.Encode.fst"
let tsym = (FStar_ToSMT_Term.mkFreeV (tname, FStar_ToSMT_Term.Type_sort))
in (
# 1537 "FStar.ToSMT.Encode.fst"
let decl = FStar_ToSMT_Term.DeclFun ((tname, [], FStar_ToSMT_Term.Type_sort, None))
in (let _139_1906 = (let _139_1905 = (primitive_type_axioms t tname tsym)
in (decl)::_139_1905)
in (_139_1906, (push_free_tvar env t tname (Some (tsym))))))))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _50_2469, datas, quals, _50_2473) -> begin
(
# 1541 "FStar.ToSMT.Encode.fst"
let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _50_19 -> (match (_50_19) with
| (FStar_Absyn_Syntax.Logic) | (FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _50_2480 -> begin
false
end))))
in (
# 1542 "FStar.ToSMT.Encode.fst"
let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(
# 1544 "FStar.ToSMT.Encode.fst"
let _50_2490 = c
in (match (_50_2490) with
| (name, args, _50_2487, _50_2489) -> begin
(let _139_1912 = (let _139_1911 = (let _139_1910 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _139_1910, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_139_1911))
in (_139_1912)::[])
end))
end else begin
(FStar_ToSMT_Term.constructor_to_decl c)
end)
in (
# 1548 "FStar.ToSMT.Encode.fst"
let inversion_axioms = (fun tapp vars -> if (((FStar_List.length datas) = 0) || (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _139_1918 = (FStar_Tc_Env.lookup_qname env.tcenv l)
in (FStar_All.pipe_right _139_1918 FStar_Option.isNone)))))) then begin
[]
end else begin
(
# 1552 "FStar.ToSMT.Encode.fst"
let _50_2497 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_50_2497) with
| (xxsym, xx) -> begin
(
# 1553 "FStar.ToSMT.Encode.fst"
let _50_2540 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _50_2500 l -> (match (_50_2500) with
| (out, decls) -> begin
(
# 1554 "FStar.ToSMT.Encode.fst"
let data_t = (FStar_Tc_Env.lookup_datacon env.tcenv l)
in (
# 1555 "FStar.ToSMT.Encode.fst"
let _50_2510 = (match ((FStar_Absyn_Util.function_formals data_t)) with
| Some (formals, res) -> begin
(formals, (FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_50_2510) with
| (args, res) -> begin
(
# 1558 "FStar.ToSMT.Encode.fst"
let indices = (match ((let _139_1921 = (FStar_Absyn_Util.compress_typ res)
in _139_1921.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (_50_2512, indices) -> begin
indices
end
| _50_2517 -> begin
[]
end)
in (
# 1561 "FStar.ToSMT.Encode.fst"
let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (a) -> begin
(let _139_1926 = (let _139_1925 = (let _139_1924 = (mk_typ_projector_name l a.FStar_Absyn_Syntax.v)
in (_139_1924, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _139_1925))
in (push_typ_var env a.FStar_Absyn_Syntax.v _139_1926))
end
| FStar_Util.Inr (x) -> begin
(let _139_1929 = (let _139_1928 = (let _139_1927 = (mk_term_projector_name l x.FStar_Absyn_Syntax.v)
in (_139_1927, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _139_1928))
in (push_term_var env x.FStar_Absyn_Syntax.v _139_1929))
end)) env))
in (
# 1564 "FStar.ToSMT.Encode.fst"
let _50_2528 = (encode_args indices env)
in (match (_50_2528) with
| (indices, decls') -> begin
(
# 1565 "FStar.ToSMT.Encode.fst"
let _50_2529 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (
# 1567 "FStar.ToSMT.Encode.fst"
let eqs = (let _139_1936 = (FStar_List.map2 (fun v a -> (match (a) with
| FStar_Util.Inl (a) -> begin
(let _139_1933 = (let _139_1932 = (FStar_ToSMT_Term.mkFreeV v)
in (_139_1932, a))
in (FStar_ToSMT_Term.mkEq _139_1933))
end
| FStar_Util.Inr (a) -> begin
(let _139_1935 = (let _139_1934 = (FStar_ToSMT_Term.mkFreeV v)
in (_139_1934, a))
in (FStar_ToSMT_Term.mkEq _139_1935))
end)) vars indices)
in (FStar_All.pipe_right _139_1936 FStar_ToSMT_Term.mk_and_l))
in (let _139_1941 = (let _139_1940 = (let _139_1939 = (let _139_1938 = (let _139_1937 = (mk_data_tester env l xx)
in (_139_1937, eqs))
in (FStar_ToSMT_Term.mkAnd _139_1938))
in (out, _139_1939))
in (FStar_ToSMT_Term.mkOr _139_1940))
in (_139_1941, (FStar_List.append decls decls')))))
end))))
end)))
end)) (FStar_ToSMT_Term.mkFalse, [])))
in (match (_50_2540) with
| (data_ax, decls) -> begin
(
# 1571 "FStar.ToSMT.Encode.fst"
let _50_2543 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_50_2543) with
| (ffsym, ff) -> begin
(
# 1572 "FStar.ToSMT.Encode.fst"
let xx_has_type = (let _139_1942 = (FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_ToSMT_Term.mk_HasTypeFuel _139_1942 xx tapp))
in (let _139_1949 = (let _139_1948 = (let _139_1947 = (let _139_1946 = (let _139_1945 = (let _139_1944 = (add_fuel (ffsym, FStar_ToSMT_Term.Fuel_sort) (((xxsym, FStar_ToSMT_Term.Term_sort))::vars))
in (let _139_1943 = (FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _139_1944, _139_1943)))
in (FStar_ToSMT_Term.mkForall _139_1945))
in (_139_1946, Some ("inversion axiom")))
in FStar_ToSMT_Term.Assume (_139_1947))
in (_139_1948)::[])
in (FStar_List.append decls _139_1949)))
end))
end))
end))
end)
in (
# 1576 "FStar.ToSMT.Encode.fst"
let k = (FStar_Absyn_Util.close_kind tps k)
in (
# 1577 "FStar.ToSMT.Encode.fst"
let _50_2555 = (match ((let _139_1950 = (FStar_Absyn_Util.compress_kind k)
in _139_1950.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_arrow (bs, res) -> begin
(true, bs, res)
end
| _50_2551 -> begin
(false, [], k)
end)
in (match (_50_2555) with
| (is_kind_arrow, formals, res) -> begin
(
# 1580 "FStar.ToSMT.Encode.fst"
let _50_2562 = (encode_binders None formals env)
in (match (_50_2562) with
| (vars, guards, env', binder_decls, _50_2561) -> begin
(
# 1582 "FStar.ToSMT.Encode.fst"
let projection_axioms = (fun tapp vars -> (match ((FStar_All.pipe_right quals (FStar_Util.find_opt (fun _50_20 -> (match (_50_20) with
| FStar_Absyn_Syntax.Projector (_50_2568) -> begin
true
end
| _50_2571 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.Projector (d, FStar_Util.Inl (a))) -> begin
(
# 1585 "FStar.ToSMT.Encode.fst"
let rec projectee = (fun i _50_21 -> (match (_50_21) with
| [] -> begin
i
end
| f::tl -> begin
(match ((Prims.fst f)) with
| FStar_Util.Inl (_50_2586) -> begin
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
# 1593 "FStar.ToSMT.Encode.fst"
let projectee_pos = (projectee 0 formals)
in (
# 1594 "FStar.ToSMT.Encode.fst"
let _50_2601 = (match ((FStar_Util.first_N projectee_pos vars)) with
| (_50_2592, xx::suffix) -> begin
(xx, suffix)
end
| _50_2598 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_50_2601) with
| (xx, suffix) -> begin
(
# 1597 "FStar.ToSMT.Encode.fst"
let dproj_app = (let _139_1964 = (let _139_1963 = (let _139_1962 = (mk_typ_projector_name d a)
in (let _139_1961 = (let _139_1960 = (FStar_ToSMT_Term.mkFreeV xx)
in (_139_1960)::[])
in (_139_1962, _139_1961)))
in (FStar_ToSMT_Term.mkApp _139_1963))
in (mk_ApplyT _139_1964 suffix))
in (let _139_1969 = (let _139_1968 = (let _139_1967 = (let _139_1966 = (let _139_1965 = (FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in (((tapp)::[])::[], vars, _139_1965))
in (FStar_ToSMT_Term.mkForall _139_1966))
in (_139_1967, Some ("projector axiom")))
in FStar_ToSMT_Term.Assume (_139_1968))
in (_139_1969)::[]))
end))))
end
| _50_2604 -> begin
[]
end))
in (
# 1601 "FStar.ToSMT.Encode.fst"
let pretype_axioms = (fun tapp vars -> (
# 1602 "FStar.ToSMT.Encode.fst"
let _50_2610 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_50_2610) with
| (xxsym, xx) -> begin
(
# 1603 "FStar.ToSMT.Encode.fst"
let _50_2613 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_50_2613) with
| (ffsym, ff) -> begin
(
# 1604 "FStar.ToSMT.Encode.fst"
let xx_has_type = (FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _139_1982 = (let _139_1981 = (let _139_1980 = (let _139_1979 = (let _139_1978 = (let _139_1977 = (let _139_1976 = (let _139_1975 = (let _139_1974 = (FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _139_1974))
in (FStar_ToSMT_Term.mkEq _139_1975))
in (xx_has_type, _139_1976))
in (FStar_ToSMT_Term.mkImp _139_1977))
in (((xx_has_type)::[])::[], ((xxsym, FStar_ToSMT_Term.Term_sort))::((ffsym, FStar_ToSMT_Term.Fuel_sort))::vars, _139_1978))
in (FStar_ToSMT_Term.mkForall _139_1979))
in (_139_1980, Some ("pretyping")))
in FStar_ToSMT_Term.Assume (_139_1981))
in (_139_1982)::[]))
end))
end)))
in (
# 1608 "FStar.ToSMT.Encode.fst"
let _50_2618 = (new_typ_constant_and_tok_from_lid env t)
in (match (_50_2618) with
| (tname, ttok, env) -> begin
(
# 1609 "FStar.ToSMT.Encode.fst"
let ttok_tm = (FStar_ToSMT_Term.mkApp (ttok, []))
in (
# 1610 "FStar.ToSMT.Encode.fst"
let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (
# 1611 "FStar.ToSMT.Encode.fst"
let tapp = (let _139_1984 = (let _139_1983 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _139_1983))
in (FStar_ToSMT_Term.mkApp _139_1984))
in (
# 1612 "FStar.ToSMT.Encode.fst"
let _50_2639 = (
# 1613 "FStar.ToSMT.Encode.fst"
let tname_decl = (let _139_1988 = (let _139_1987 = (FStar_All.pipe_right vars (FStar_List.map (fun _50_2624 -> (match (_50_2624) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _139_1986 = (varops.next_id ())
in (tname, _139_1987, FStar_ToSMT_Term.Type_sort, _139_1986)))
in (constructor_or_logic_type_decl _139_1988))
in (
# 1614 "FStar.ToSMT.Encode.fst"
let _50_2636 = (match (vars) with
| [] -> begin
(let _139_1992 = (let _139_1991 = (let _139_1990 = (FStar_ToSMT_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _139_1989 -> Some (_139_1989)) _139_1990))
in (push_free_tvar env t tname _139_1991))
in ([], _139_1992))
end
| _50_2628 -> begin
(
# 1617 "FStar.ToSMT.Encode.fst"
let ttok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, Some ("token")))
in (
# 1618 "FStar.ToSMT.Encode.fst"
let ttok_fresh = (let _139_1993 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _139_1993))
in (
# 1619 "FStar.ToSMT.Encode.fst"
let ttok_app = (mk_ApplyT ttok_tm vars)
in (
# 1620 "FStar.ToSMT.Encode.fst"
let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (
# 1627 "FStar.ToSMT.Encode.fst"
let name_tok_corr = (let _139_1997 = (let _139_1996 = (let _139_1995 = (let _139_1994 = (FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _139_1994))
in (FStar_ToSMT_Term.mkForall' _139_1995))
in (_139_1996, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_139_1997))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_50_2636) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_50_2639) with
| (decls, env) -> begin
(
# 1630 "FStar.ToSMT.Encode.fst"
let kindingAx = (
# 1631 "FStar.ToSMT.Encode.fst"
let _50_2642 = (encode_knd res env' tapp)
in (match (_50_2642) with
| (k, decls) -> begin
(
# 1632 "FStar.ToSMT.Encode.fst"
let karr = if is_kind_arrow then begin
(let _139_2001 = (let _139_2000 = (let _139_1999 = (let _139_1998 = (FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _139_1998))
in (_139_1999, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_139_2000))
in (_139_2001)::[])
end else begin
[]
end
in (let _139_2007 = (let _139_2006 = (let _139_2005 = (let _139_2004 = (let _139_2003 = (let _139_2002 = (FStar_ToSMT_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _139_2002))
in (FStar_ToSMT_Term.mkForall _139_2003))
in (_139_2004, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_139_2005))
in (_139_2006)::[])
in (FStar_List.append (FStar_List.append decls karr) _139_2007)))
end))
in (
# 1637 "FStar.ToSMT.Encode.fst"
let aux = if is_logical then begin
(let _139_2008 = (projection_axioms tapp vars)
in (FStar_List.append kindingAx _139_2008))
end else begin
(let _139_2015 = (let _139_2013 = (let _139_2011 = (let _139_2009 = (primitive_type_axioms t tname tapp)
in (FStar_List.append kindingAx _139_2009))
in (let _139_2010 = (inversion_axioms tapp vars)
in (FStar_List.append _139_2011 _139_2010)))
in (let _139_2012 = (projection_axioms tapp vars)
in (FStar_List.append _139_2013 _139_2012)))
in (let _139_2014 = (pretype_axioms tapp vars)
in (FStar_List.append _139_2015 _139_2014)))
end
in (
# 1646 "FStar.ToSMT.Encode.fst"
let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))))
end))
end))))))
end
| FStar_Absyn_Syntax.Sig_datacon (d, _50_2649, _50_2651, _50_2653, _50_2655, _50_2657) when (FStar_Ident.lid_equals d FStar_Absyn_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_datacon (d, t, (_50_2663, tps, _50_2666), quals, _50_2670, drange) -> begin
(
# 1654 "FStar.ToSMT.Encode.fst"
let t = (let _139_2017 = (FStar_List.map (fun _50_2677 -> (match (_50_2677) with
| (x, _50_2676) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit (true)))
end)) tps)
in (FStar_Absyn_Util.close_typ _139_2017 t))
in (
# 1655 "FStar.ToSMT.Encode.fst"
let _50_2682 = (new_term_constant_and_tok_from_lid env d)
in (match (_50_2682) with
| (ddconstrsym, ddtok, env) -> begin
(
# 1656 "FStar.ToSMT.Encode.fst"
let ddtok_tm = (FStar_ToSMT_Term.mkApp (ddtok, []))
in (
# 1657 "FStar.ToSMT.Encode.fst"
let _50_2691 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
(f, (FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_50_2691) with
| (formals, t_res) -> begin
(
# 1660 "FStar.ToSMT.Encode.fst"
let _50_2694 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_50_2694) with
| (fuel_var, fuel_tm) -> begin
(
# 1661 "FStar.ToSMT.Encode.fst"
let s_fuel_tm = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (
# 1662 "FStar.ToSMT.Encode.fst"
let _50_2701 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_50_2701) with
| (vars, guards, env', binder_decls, names) -> begin
(
# 1663 "FStar.ToSMT.Encode.fst"
let projectors = (FStar_All.pipe_right names (FStar_List.map (fun _50_22 -> (match (_50_22) with
| FStar_Util.Inl (a) -> begin
(let _139_2019 = (mk_typ_projector_name d a)
in (_139_2019, FStar_ToSMT_Term.Type_sort))
end
| FStar_Util.Inr (x) -> begin
(let _139_2020 = (mk_term_projector_name d x)
in (_139_2020, FStar_ToSMT_Term.Term_sort))
end))))
in (
# 1666 "FStar.ToSMT.Encode.fst"
let datacons = (let _139_2022 = (let _139_2021 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_ToSMT_Term.Term_sort, _139_2021))
in (FStar_All.pipe_right _139_2022 FStar_ToSMT_Term.constructor_to_decl))
in (
# 1667 "FStar.ToSMT.Encode.fst"
let app = (mk_ApplyE ddtok_tm vars)
in (
# 1668 "FStar.ToSMT.Encode.fst"
let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (
# 1669 "FStar.ToSMT.Encode.fst"
let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (
# 1670 "FStar.ToSMT.Encode.fst"
let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (
# 1672 "FStar.ToSMT.Encode.fst"
let _50_2715 = (encode_typ_pred None t env ddtok_tm)
in (match (_50_2715) with
| (tok_typing, decls3) -> begin
(
# 1674 "FStar.ToSMT.Encode.fst"
let _50_2722 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_50_2722) with
| (vars', guards', env'', decls_formals, _50_2721) -> begin
(
# 1675 "FStar.ToSMT.Encode.fst"
let _50_2727 = (
# 1676 "FStar.ToSMT.Encode.fst"
let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars')
in (
# 1677 "FStar.ToSMT.Encode.fst"
let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_50_2727) with
| (ty_pred', decls_pred) -> begin
(
# 1679 "FStar.ToSMT.Encode.fst"
let guard' = (FStar_ToSMT_Term.mk_and_l guards')
in (
# 1680 "FStar.ToSMT.Encode.fst"
let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _50_2731 -> begin
(let _139_2024 = (let _139_2023 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ddtok, FStar_ToSMT_Term.Term_sort) _139_2023))
in (_139_2024)::[])
end)
in (
# 1684 "FStar.ToSMT.Encode.fst"
let encode_elim = (fun _50_2734 -> (match (()) with
| () -> begin
(
# 1685 "FStar.ToSMT.Encode.fst"
let _50_2737 = (FStar_Absyn_Util.head_and_args t_res)
in (match (_50_2737) with
| (head, args) -> begin
(match ((let _139_2027 = (FStar_Absyn_Util.compress_typ head)
in _139_2027.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(
# 1688 "FStar.ToSMT.Encode.fst"
let encoded_head = (lookup_free_tvar_name env' fv)
in (
# 1689 "FStar.ToSMT.Encode.fst"
let _50_2743 = (encode_args args env')
in (match (_50_2743) with
| (encoded_args, arg_decls) -> begin
(
# 1690 "FStar.ToSMT.Encode.fst"
let _50_2767 = (FStar_List.fold_left (fun _50_2747 arg -> (match (_50_2747) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| FStar_Util.Inl (targ) -> begin
(
# 1693 "FStar.ToSMT.Encode.fst"
let _50_2755 = (let _139_2030 = (FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _139_2030))
in (match (_50_2755) with
| (_50_2752, tv, env) -> begin
(let _139_2032 = (let _139_2031 = (FStar_ToSMT_Term.mkEq (targ, tv))
in (_139_2031)::eqns)
in (env, (tv)::arg_vars, _139_2032))
end))
end
| FStar_Util.Inr (varg) -> begin
(
# 1696 "FStar.ToSMT.Encode.fst"
let _50_2762 = (let _139_2033 = (FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _139_2033))
in (match (_50_2762) with
| (_50_2759, xv, env) -> begin
(let _139_2035 = (let _139_2034 = (FStar_ToSMT_Term.mkEq (varg, xv))
in (_139_2034)::eqns)
in (env, (xv)::arg_vars, _139_2035))
end))
end)
end)) (env', [], []) encoded_args)
in (match (_50_2767) with
| (_50_2764, arg_vars, eqns) -> begin
(
# 1698 "FStar.ToSMT.Encode.fst"
let arg_vars = (FStar_List.rev arg_vars)
in (
# 1699 "FStar.ToSMT.Encode.fst"
let ty = (FStar_ToSMT_Term.mkApp (encoded_head, arg_vars))
in (
# 1700 "FStar.ToSMT.Encode.fst"
let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (
# 1701 "FStar.ToSMT.Encode.fst"
let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (
# 1702 "FStar.ToSMT.Encode.fst"
let ty_pred = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (
# 1703 "FStar.ToSMT.Encode.fst"
let arg_binders = (FStar_List.map FStar_ToSMT_Term.fv_of_term arg_vars)
in (
# 1704 "FStar.ToSMT.Encode.fst"
let typing_inversion = (let _139_2042 = (let _139_2041 = (let _139_2040 = (let _139_2039 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _139_2038 = (let _139_2037 = (let _139_2036 = (FStar_ToSMT_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _139_2036))
in (FStar_ToSMT_Term.mkImp _139_2037))
in (((ty_pred)::[])::[], _139_2039, _139_2038)))
in (FStar_ToSMT_Term.mkForall _139_2040))
in (_139_2041, Some ("data constructor typing elim")))
in FStar_ToSMT_Term.Assume (_139_2042))
in (
# 1709 "FStar.ToSMT.Encode.fst"
let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Absyn_Const.lextop_lid) then begin
(
# 1711 "FStar.ToSMT.Encode.fst"
let x = (let _139_2043 = (varops.fresh "x")
in (_139_2043, FStar_ToSMT_Term.Term_sort))
in (
# 1712 "FStar.ToSMT.Encode.fst"
let xtm = (FStar_ToSMT_Term.mkFreeV x)
in (let _139_2053 = (let _139_2052 = (let _139_2051 = (let _139_2050 = (let _139_2045 = (let _139_2044 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_139_2044)::[])
in (_139_2045)::[])
in (let _139_2049 = (let _139_2048 = (let _139_2047 = (FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _139_2046 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_139_2047, _139_2046)))
in (FStar_ToSMT_Term.mkImp _139_2048))
in (_139_2050, (x)::[], _139_2049)))
in (FStar_ToSMT_Term.mkForall _139_2051))
in (_139_2052, Some ("lextop is top")))
in FStar_ToSMT_Term.Assume (_139_2053))))
end else begin
(
# 1715 "FStar.ToSMT.Encode.fst"
let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| (FStar_ToSMT_Term.Type_sort) | (FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| FStar_ToSMT_Term.Term_sort -> begin
(let _139_2056 = (let _139_2055 = (FStar_ToSMT_Term.mkFreeV v)
in (FStar_ToSMT_Term.mk_Precedes _139_2055 dapp))
in (_139_2056)::[])
end
| _50_2782 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _139_2063 = (let _139_2062 = (let _139_2061 = (let _139_2060 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _139_2059 = (let _139_2058 = (let _139_2057 = (FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _139_2057))
in (FStar_ToSMT_Term.mkImp _139_2058))
in (((ty_pred)::[])::[], _139_2060, _139_2059)))
in (FStar_ToSMT_Term.mkForall _139_2061))
in (_139_2062, Some ("subterm ordering")))
in FStar_ToSMT_Term.Assume (_139_2063)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _50_2786 -> begin
(
# 1724 "FStar.ToSMT.Encode.fst"
let _50_2787 = (let _139_2066 = (let _139_2065 = (FStar_Absyn_Print.sli d)
in (let _139_2064 = (FStar_Absyn_Print.typ_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _139_2065 _139_2064)))
in (FStar_Tc_Errors.warn drange _139_2066))
in ([], []))
end)
end))
end))
in (
# 1726 "FStar.ToSMT.Encode.fst"
let _50_2791 = (encode_elim ())
in (match (_50_2791) with
| (decls2, elim) -> begin
(
# 1727 "FStar.ToSMT.Encode.fst"
let g = (let _139_2091 = (let _139_2090 = (let _139_2075 = (let _139_2074 = (let _139_2073 = (let _139_2072 = (let _139_2071 = (let _139_2070 = (let _139_2069 = (let _139_2068 = (let _139_2067 = (FStar_Absyn_Print.sli d)
in (FStar_Util.format1 "data constructor proxy: %s" _139_2067))
in Some (_139_2068))
in (ddtok, [], FStar_ToSMT_Term.Term_sort, _139_2069))
in FStar_ToSMT_Term.DeclFun (_139_2070))
in (_139_2071)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _139_2072))
in (FStar_List.append _139_2073 proxy_fresh))
in (FStar_List.append _139_2074 decls_formals))
in (FStar_List.append _139_2075 decls_pred))
in (let _139_2089 = (let _139_2088 = (let _139_2087 = (let _139_2079 = (let _139_2078 = (let _139_2077 = (let _139_2076 = (FStar_ToSMT_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _139_2076))
in (FStar_ToSMT_Term.mkForall _139_2077))
in (_139_2078, Some ("equality for proxy")))
in FStar_ToSMT_Term.Assume (_139_2079))
in (let _139_2086 = (let _139_2085 = (let _139_2084 = (let _139_2083 = (let _139_2082 = (let _139_2081 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) vars')
in (let _139_2080 = (FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _139_2081, _139_2080)))
in (FStar_ToSMT_Term.mkForall _139_2082))
in (_139_2083, Some ("data constructor typing intro")))
in FStar_ToSMT_Term.Assume (_139_2084))
in (_139_2085)::[])
in (_139_2087)::_139_2086))
in (FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_139_2088)
in (FStar_List.append _139_2090 _139_2089)))
in (FStar_List.append _139_2091 elim))
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
| FStar_Absyn_Syntax.Sig_bundle (ses, _50_2795, _50_2797, _50_2799) -> begin
(
# 1743 "FStar.ToSMT.Encode.fst"
let _50_2804 = (encode_signature env ses)
in (match (_50_2804) with
| (g, env) -> begin
(
# 1744 "FStar.ToSMT.Encode.fst"
let _50_2816 = (FStar_All.pipe_right g (FStar_List.partition (fun _50_23 -> (match (_50_23) with
| FStar_ToSMT_Term.Assume (_50_2807, Some ("inversion axiom")) -> begin
false
end
| _50_2813 -> begin
true
end))))
in (match (_50_2816) with
| (g', inversions) -> begin
(
# 1747 "FStar.ToSMT.Encode.fst"
let _50_2825 = (FStar_All.pipe_right g' (FStar_List.partition (fun _50_24 -> (match (_50_24) with
| FStar_ToSMT_Term.DeclFun (_50_2819) -> begin
true
end
| _50_2822 -> begin
false
end))))
in (match (_50_2825) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_let (_50_2827, _50_2829, _50_2831, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _50_25 -> (match (_50_25) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _50_2843 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_let ((is_rec, bindings), _50_2848, _50_2850, quals) -> begin
(
# 1756 "FStar.ToSMT.Encode.fst"
let eta_expand = (fun binders formals body t -> (
# 1757 "FStar.ToSMT.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1758 "FStar.ToSMT.Encode.fst"
let _50_2862 = (FStar_Util.first_N nbinders formals)
in (match (_50_2862) with
| (formals, extra_formals) -> begin
(
# 1759 "FStar.ToSMT.Encode.fst"
let subst = (FStar_List.map2 (fun formal binder -> (match (((Prims.fst formal), (Prims.fst binder))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _139_2106 = (let _139_2105 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _139_2105))
in FStar_Util.Inl (_139_2106))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _139_2108 = (let _139_2107 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _139_2107))
in FStar_Util.Inr (_139_2108))
end
| _50_2876 -> begin
(FStar_All.failwith "Impossible")
end)) formals binders)
in (
# 1763 "FStar.ToSMT.Encode.fst"
let extra_formals = (let _139_2109 = (FStar_Absyn_Util.subst_binders subst extra_formals)
in (FStar_All.pipe_right _139_2109 FStar_Absyn_Util.name_binders))
in (
# 1764 "FStar.ToSMT.Encode.fst"
let body = (let _139_2115 = (let _139_2111 = (let _139_2110 = (FStar_Absyn_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _139_2110))
in (body, _139_2111))
in (let _139_2114 = (let _139_2113 = (FStar_Absyn_Util.subst_typ subst t)
in (FStar_All.pipe_left (fun _139_2112 -> Some (_139_2112)) _139_2113))
in (FStar_Absyn_Syntax.mk_Exp_app_flat _139_2115 _139_2114 body.FStar_Absyn_Syntax.pos)))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (
# 1767 "FStar.ToSMT.Encode.fst"
let destruct_bound_function = (fun flid t_norm e -> (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_ascribed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (binders, body); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _, _)) | (FStar_Absyn_Syntax.Exp_abs (binders, body)) -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(
# 1772 "FStar.ToSMT.Encode.fst"
let nformals = (FStar_List.length formals)
in (
# 1773 "FStar.ToSMT.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1774 "FStar.ToSMT.Encode.fst"
let tres = (FStar_Absyn_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Absyn_Util.is_total_comp c)) then begin
(
# 1776 "FStar.ToSMT.Encode.fst"
let _50_2914 = (FStar_Util.first_N nformals binders)
in (match (_50_2914) with
| (bs0, rest) -> begin
(
# 1777 "FStar.ToSMT.Encode.fst"
let tres = (match ((FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tres)
end
| _50_2918 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 1780 "FStar.ToSMT.Encode.fst"
let body = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (tres)) body.FStar_Absyn_Syntax.pos)
in (bs0, body, bs0, tres)))
end))
end else begin
if (nformals > nbinders) then begin
(
# 1784 "FStar.ToSMT.Encode.fst"
let _50_2923 = (eta_expand binders formals body tres)
in (match (_50_2923) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end
| _50_2925 -> begin
(let _139_2124 = (let _139_2123 = (FStar_Absyn_Print.exp_to_string e)
in (let _139_2122 = (FStar_Absyn_Print.typ_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _139_2123 _139_2122)))
in (FStar_All.failwith _139_2124))
end)
end
| _50_2927 -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(
# 1795 "FStar.ToSMT.Encode.fst"
let tres = (FStar_Absyn_Util.comp_result c)
in (
# 1796 "FStar.ToSMT.Encode.fst"
let _50_2935 = (eta_expand [] formals e tres)
in (match (_50_2935) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _50_2937 -> begin
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
| _50_2950 -> begin
false
end)))) || (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp))))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(
# 1805 "FStar.ToSMT.Encode.fst"
let _50_2969 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _50_2956 lb -> (match (_50_2956) with
| (toks, typs, decls, env) -> begin
(
# 1807 "FStar.ToSMT.Encode.fst"
let _50_2958 = if (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (
# 1808 "FStar.ToSMT.Encode.fst"
let t_norm = (let _139_2130 = (whnf env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_right _139_2130 FStar_Absyn_Util.compress_typ))
in (
# 1809 "FStar.ToSMT.Encode.fst"
let _50_2964 = (let _139_2131 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _139_2131 lb.FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_50_2964) with
| (tok, decl, env) -> begin
(let _139_2134 = (let _139_2133 = (let _139_2132 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (_139_2132, tok))
in (_139_2133)::toks)
in (_139_2134, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_50_2969) with
| (toks, typs, decls, env) -> begin
(
# 1811 "FStar.ToSMT.Encode.fst"
let toks = (FStar_List.rev toks)
in (
# 1812 "FStar.ToSMT.Encode.fst"
let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (
# 1813 "FStar.ToSMT.Encode.fst"
let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _50_27 -> (match (_50_27) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _50_2976 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> ((FStar_Absyn_Util.is_lemma t) || (let _139_2137 = (FStar_Absyn_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _139_2137))))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Absyn_Syntax.lbname = _50_2984; FStar_Absyn_Syntax.lbtyp = _50_2982; FStar_Absyn_Syntax.lbeff = _50_2980; FStar_Absyn_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(
# 1820 "FStar.ToSMT.Encode.fst"
let _50_3000 = (destruct_bound_function flid t_norm e)
in (match (_50_3000) with
| (binders, body, formals, tres) -> begin
(
# 1821 "FStar.ToSMT.Encode.fst"
let _50_3007 = (encode_binders None binders env)
in (match (_50_3007) with
| (vars, guards, env', binder_decls, _50_3006) -> begin
(
# 1822 "FStar.ToSMT.Encode.fst"
let app = (match (vars) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
end
| _50_3010 -> begin
(let _139_2139 = (let _139_2138 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (f, _139_2138))
in (FStar_ToSMT_Term.mkApp _139_2139))
end)
in (
# 1823 "FStar.ToSMT.Encode.fst"
let _50_3014 = (encode_exp body env')
in (match (_50_3014) with
| (body, decls2) -> begin
(
# 1824 "FStar.ToSMT.Encode.fst"
let eqn = (let _139_2148 = (let _139_2147 = (let _139_2144 = (let _139_2143 = (let _139_2142 = (let _139_2141 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _139_2140 = (FStar_ToSMT_Term.mkEq (app, body))
in (_139_2141, _139_2140)))
in (FStar_ToSMT_Term.mkImp _139_2142))
in (((app)::[])::[], vars, _139_2143))
in (FStar_ToSMT_Term.mkForall _139_2144))
in (let _139_2146 = (let _139_2145 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_139_2145))
in (_139_2147, _139_2146)))
in FStar_ToSMT_Term.Assume (_139_2148))
in ((FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end))
end
| _50_3017 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 1827 "FStar.ToSMT.Encode.fst"
let fuel = (let _139_2149 = (varops.fresh "fuel")
in (_139_2149, FStar_ToSMT_Term.Fuel_sort))
in (
# 1828 "FStar.ToSMT.Encode.fst"
let fuel_tm = (FStar_ToSMT_Term.mkFreeV fuel)
in (
# 1829 "FStar.ToSMT.Encode.fst"
let env0 = env
in (
# 1830 "FStar.ToSMT.Encode.fst"
let _50_3034 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _50_3023 _50_3028 -> (match ((_50_3023, _50_3028)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(
# 1831 "FStar.ToSMT.Encode.fst"
let g = (varops.new_fvar flid)
in (
# 1832 "FStar.ToSMT.Encode.fst"
let gtok = (varops.new_fvar flid)
in (
# 1833 "FStar.ToSMT.Encode.fst"
let env = (let _139_2154 = (let _139_2153 = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _139_2152 -> Some (_139_2152)) _139_2153))
in (push_free_var env flid gtok _139_2154))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_50_3034) with
| (gtoks, env) -> begin
(
# 1835 "FStar.ToSMT.Encode.fst"
let gtoks = (FStar_List.rev gtoks)
in (
# 1836 "FStar.ToSMT.Encode.fst"
let encode_one_binding = (fun env0 _50_3043 t_norm _50_3052 -> (match ((_50_3043, _50_3052)) with
| ((flid, f, ftok, g, gtok), {FStar_Absyn_Syntax.lbname = _50_3051; FStar_Absyn_Syntax.lbtyp = _50_3049; FStar_Absyn_Syntax.lbeff = _50_3047; FStar_Absyn_Syntax.lbdef = e}) -> begin
(
# 1837 "FStar.ToSMT.Encode.fst"
let _50_3057 = (destruct_bound_function flid t_norm e)
in (match (_50_3057) with
| (binders, body, formals, tres) -> begin
(
# 1838 "FStar.ToSMT.Encode.fst"
let _50_3064 = (encode_binders None binders env)
in (match (_50_3064) with
| (vars, guards, env', binder_decls, _50_3063) -> begin
(
# 1839 "FStar.ToSMT.Encode.fst"
let decl_g = (let _139_2165 = (let _139_2164 = (let _139_2163 = (FStar_List.map Prims.snd vars)
in (FStar_ToSMT_Term.Fuel_sort)::_139_2163)
in (g, _139_2164, FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_ToSMT_Term.DeclFun (_139_2165))
in (
# 1840 "FStar.ToSMT.Encode.fst"
let env0 = (push_zfuel_name env0 flid g)
in (
# 1841 "FStar.ToSMT.Encode.fst"
let decl_g_tok = FStar_ToSMT_Term.DeclFun ((gtok, [], FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (
# 1842 "FStar.ToSMT.Encode.fst"
let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (
# 1843 "FStar.ToSMT.Encode.fst"
let app = (FStar_ToSMT_Term.mkApp (f, vars_tm))
in (
# 1844 "FStar.ToSMT.Encode.fst"
let gsapp = (let _139_2168 = (let _139_2167 = (let _139_2166 = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_139_2166)::vars_tm)
in (g, _139_2167))
in (FStar_ToSMT_Term.mkApp _139_2168))
in (
# 1845 "FStar.ToSMT.Encode.fst"
let gmax = (let _139_2171 = (let _139_2170 = (let _139_2169 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_139_2169)::vars_tm)
in (g, _139_2170))
in (FStar_ToSMT_Term.mkApp _139_2171))
in (
# 1846 "FStar.ToSMT.Encode.fst"
let _50_3074 = (encode_exp body env')
in (match (_50_3074) with
| (body_tm, decls2) -> begin
(
# 1847 "FStar.ToSMT.Encode.fst"
let eqn_g = (let _139_2180 = (let _139_2179 = (let _139_2176 = (let _139_2175 = (let _139_2174 = (let _139_2173 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _139_2172 = (FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_139_2173, _139_2172)))
in (FStar_ToSMT_Term.mkImp _139_2174))
in (((gsapp)::[])::[], (fuel)::vars, _139_2175))
in (FStar_ToSMT_Term.mkForall _139_2176))
in (let _139_2178 = (let _139_2177 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_139_2177))
in (_139_2179, _139_2178)))
in FStar_ToSMT_Term.Assume (_139_2180))
in (
# 1848 "FStar.ToSMT.Encode.fst"
let eqn_f = (let _139_2184 = (let _139_2183 = (let _139_2182 = (let _139_2181 = (FStar_ToSMT_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _139_2181))
in (FStar_ToSMT_Term.mkForall _139_2182))
in (_139_2183, Some ("Correspondence of recursive function to instrumented version")))
in FStar_ToSMT_Term.Assume (_139_2184))
in (
# 1849 "FStar.ToSMT.Encode.fst"
let eqn_g' = (let _139_2193 = (let _139_2192 = (let _139_2191 = (let _139_2190 = (let _139_2189 = (let _139_2188 = (let _139_2187 = (let _139_2186 = (let _139_2185 = (FStar_ToSMT_Term.n_fuel 0)
in (_139_2185)::vars_tm)
in (g, _139_2186))
in (FStar_ToSMT_Term.mkApp _139_2187))
in (gsapp, _139_2188))
in (FStar_ToSMT_Term.mkEq _139_2189))
in (((gsapp)::[])::[], (fuel)::vars, _139_2190))
in (FStar_ToSMT_Term.mkForall _139_2191))
in (_139_2192, Some ("Fuel irrelevance")))
in FStar_ToSMT_Term.Assume (_139_2193))
in (
# 1850 "FStar.ToSMT.Encode.fst"
let _50_3097 = (
# 1851 "FStar.ToSMT.Encode.fst"
let _50_3084 = (encode_binders None formals env0)
in (match (_50_3084) with
| (vars, v_guards, env, binder_decls, _50_3083) -> begin
(
# 1852 "FStar.ToSMT.Encode.fst"
let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (
# 1853 "FStar.ToSMT.Encode.fst"
let gapp = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (
# 1854 "FStar.ToSMT.Encode.fst"
let tok_corr = (
# 1855 "FStar.ToSMT.Encode.fst"
let tok_app = (let _139_2194 = (FStar_ToSMT_Term.mkFreeV (gtok, FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _139_2194 ((fuel)::vars)))
in (let _139_2198 = (let _139_2197 = (let _139_2196 = (let _139_2195 = (FStar_ToSMT_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _139_2195))
in (FStar_ToSMT_Term.mkForall _139_2196))
in (_139_2197, Some ("Fuel token correspondence")))
in FStar_ToSMT_Term.Assume (_139_2198)))
in (
# 1857 "FStar.ToSMT.Encode.fst"
let _50_3094 = (
# 1858 "FStar.ToSMT.Encode.fst"
let _50_3091 = (encode_typ_pred None tres env gapp)
in (match (_50_3091) with
| (g_typing, d3) -> begin
(let _139_2206 = (let _139_2205 = (let _139_2204 = (let _139_2203 = (let _139_2202 = (let _139_2201 = (let _139_2200 = (let _139_2199 = (FStar_ToSMT_Term.mk_and_l v_guards)
in (_139_2199, g_typing))
in (FStar_ToSMT_Term.mkImp _139_2200))
in (((gapp)::[])::[], (fuel)::vars, _139_2201))
in (FStar_ToSMT_Term.mkForall _139_2202))
in (_139_2203, None))
in FStar_ToSMT_Term.Assume (_139_2204))
in (_139_2205)::[])
in (d3, _139_2206))
end))
in (match (_50_3094) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_50_3097) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (
# 1862 "FStar.ToSMT.Encode.fst"
let _50_3113 = (let _139_2209 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _50_3101 _50_3105 -> (match ((_50_3101, _50_3105)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(
# 1863 "FStar.ToSMT.Encode.fst"
let _50_3109 = (encode_one_binding env0 gtok ty bs)
in (match (_50_3109) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _139_2209))
in (match (_50_3113) with
| (decls, eqns, env0) -> begin
(
# 1865 "FStar.ToSMT.Encode.fst"
let _50_3122 = (let _139_2211 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _139_2211 (FStar_List.partition (fun _50_28 -> (match (_50_28) with
| FStar_ToSMT_Term.DeclFun (_50_3116) -> begin
true
end
| _50_3119 -> begin
false
end)))))
in (match (_50_3122) with
| (prefix_decls, rest) -> begin
(
# 1868 "FStar.ToSMT.Encode.fst"
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
# 1871 "FStar.ToSMT.Encode.fst"
let msg = (let _139_2214 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname))))
in (FStar_All.pipe_right _139_2214 (FStar_String.concat " and ")))
in (
# 1872 "FStar.ToSMT.Encode.fst"
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
# 1886 "FStar.ToSMT.Encode.fst"
let _50_3149 = (encode_free_var env x t t_norm [])
in (match (_50_3149) with
| (decls, env) -> begin
(
# 1887 "FStar.ToSMT.Encode.fst"
let _50_3154 = (lookup_lid env x)
in (match (_50_3154) with
| (n, x', _50_3153) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _50_3158) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_ToSMT_Term.decl Prims.list = (fun env lid t -> (
# 1893 "FStar.ToSMT.Encode.fst"
let _50_3166 = (encode_function_type_as_formula None None t env)
in (match (_50_3166) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_ToSMT_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)))))::[]))
end)))
and encode_free_var : env_t  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.qualifier Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env lid tt t_norm quals -> if ((let _139_2227 = (FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _139_2227)) || (FStar_Absyn_Util.is_lemma t_norm)) then begin
(
# 1898 "FStar.ToSMT.Encode.fst"
let _50_3175 = (new_term_constant_and_tok_from_lid env lid)
in (match (_50_3175) with
| (vname, vtok, env) -> begin
(
# 1899 "FStar.ToSMT.Encode.fst"
let arg_sorts = (match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _50_3178) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _50_29 -> (match (_50_29) with
| (FStar_Util.Inl (_50_3183), _50_3186) -> begin
FStar_ToSMT_Term.Type_sort
end
| _50_3189 -> begin
FStar_ToSMT_Term.Term_sort
end))))
end
| _50_3191 -> begin
[]
end)
in (
# 1902 "FStar.ToSMT.Encode.fst"
let d = FStar_ToSMT_Term.DeclFun ((vname, arg_sorts, FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (
# 1903 "FStar.ToSMT.Encode.fst"
let dd = FStar_ToSMT_Term.DeclFun ((vtok, [], FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(
# 1906 "FStar.ToSMT.Encode.fst"
let vname = (varops.new_fvar lid)
in (
# 1907 "FStar.ToSMT.Encode.fst"
let definition = (prims.mk lid vname)
in (
# 1908 "FStar.ToSMT.Encode.fst"
let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(
# 1910 "FStar.ToSMT.Encode.fst"
let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (
# 1911 "FStar.ToSMT.Encode.fst"
let _50_3208 = (match ((FStar_Absyn_Util.function_formals t_norm)) with
| Some (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _139_2229 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _139_2229))
end else begin
(args, (None, (FStar_Absyn_Util.comp_result comp)))
end
end
| None -> begin
([], (None, t_norm))
end)
in (match (_50_3208) with
| (formals, (pre_opt, res_t)) -> begin
(
# 1917 "FStar.ToSMT.Encode.fst"
let _50_3212 = (new_term_constant_and_tok_from_lid env lid)
in (match (_50_3212) with
| (vname, vtok, env) -> begin
(
# 1918 "FStar.ToSMT.Encode.fst"
let vtok_tm = (match (formals) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
end
| _50_3215 -> begin
(FStar_ToSMT_Term.mkApp (vtok, []))
end)
in (
# 1921 "FStar.ToSMT.Encode.fst"
let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _50_30 -> (match (_50_30) with
| FStar_Absyn_Syntax.Discriminator (d) -> begin
(
# 1923 "FStar.ToSMT.Encode.fst"
let _50_3231 = (FStar_Util.prefix vars)
in (match (_50_3231) with
| (_50_3226, (xxsym, _50_3229)) -> begin
(
# 1924 "FStar.ToSMT.Encode.fst"
let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (let _139_2246 = (let _139_2245 = (let _139_2244 = (let _139_2243 = (let _139_2242 = (let _139_2241 = (let _139_2240 = (let _139_2239 = (FStar_ToSMT_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _139_2239))
in (vapp, _139_2240))
in (FStar_ToSMT_Term.mkEq _139_2241))
in (((vapp)::[])::[], vars, _139_2242))
in (FStar_ToSMT_Term.mkForall _139_2243))
in (_139_2244, Some ("Discriminator equation")))
in FStar_ToSMT_Term.Assume (_139_2245))
in (_139_2246)::[]))
end))
end
| FStar_Absyn_Syntax.Projector (d, FStar_Util.Inr (f)) -> begin
(
# 1929 "FStar.ToSMT.Encode.fst"
let _50_3244 = (FStar_Util.prefix vars)
in (match (_50_3244) with
| (_50_3239, (xxsym, _50_3242)) -> begin
(
# 1930 "FStar.ToSMT.Encode.fst"
let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (
# 1931 "FStar.ToSMT.Encode.fst"
let prim_app = (let _139_2248 = (let _139_2247 = (mk_term_projector_name d f)
in (_139_2247, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _139_2248))
in (let _139_2253 = (let _139_2252 = (let _139_2251 = (let _139_2250 = (let _139_2249 = (FStar_ToSMT_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _139_2249))
in (FStar_ToSMT_Term.mkForall _139_2250))
in (_139_2251, Some ("Projector equation")))
in FStar_ToSMT_Term.Assume (_139_2252))
in (_139_2253)::[])))
end))
end
| _50_3248 -> begin
[]
end)))))
in (
# 1935 "FStar.ToSMT.Encode.fst"
let _50_3255 = (encode_binders None formals env)
in (match (_50_3255) with
| (vars, guards, env', decls1, _50_3254) -> begin
(
# 1936 "FStar.ToSMT.Encode.fst"
let _50_3264 = (match (pre_opt) with
| None -> begin
(let _139_2254 = (FStar_ToSMT_Term.mk_and_l guards)
in (_139_2254, decls1))
end
| Some (p) -> begin
(
# 1938 "FStar.ToSMT.Encode.fst"
let _50_3261 = (encode_formula p env')
in (match (_50_3261) with
| (g, ds) -> begin
(let _139_2255 = (FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_139_2255, (FStar_List.append decls1 ds)))
end))
end)
in (match (_50_3264) with
| (guard, decls1) -> begin
(
# 1939 "FStar.ToSMT.Encode.fst"
let vtok_app = (mk_ApplyE vtok_tm vars)
in (
# 1941 "FStar.ToSMT.Encode.fst"
let vapp = (let _139_2257 = (let _139_2256 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (vname, _139_2256))
in (FStar_ToSMT_Term.mkApp _139_2257))
in (
# 1942 "FStar.ToSMT.Encode.fst"
let _50_3295 = (
# 1943 "FStar.ToSMT.Encode.fst"
let vname_decl = (let _139_2260 = (let _139_2259 = (FStar_All.pipe_right formals (FStar_List.map (fun _50_31 -> (match (_50_31) with
| (FStar_Util.Inl (_50_3269), _50_3272) -> begin
FStar_ToSMT_Term.Type_sort
end
| _50_3275 -> begin
FStar_ToSMT_Term.Term_sort
end))))
in (vname, _139_2259, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_139_2260))
in (
# 1944 "FStar.ToSMT.Encode.fst"
let _50_3282 = (
# 1945 "FStar.ToSMT.Encode.fst"
let env = (
# 1945 "FStar.ToSMT.Encode.fst"
let _50_3277 = env
in {bindings = _50_3277.bindings; depth = _50_3277.depth; tcenv = _50_3277.tcenv; warn = _50_3277.warn; cache = _50_3277.cache; nolabels = _50_3277.nolabels; use_zfuel_name = _50_3277.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_typ_pred None tt env vtok_tm)
end else begin
(encode_typ_pred None t_norm env vtok_tm)
end)
in (match (_50_3282) with
| (tok_typing, decls2) -> begin
(
# 1949 "FStar.ToSMT.Encode.fst"
let tok_typing = FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in (
# 1950 "FStar.ToSMT.Encode.fst"
let _50_3292 = (match (formals) with
| [] -> begin
(let _139_2264 = (let _139_2263 = (let _139_2262 = (FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
in (FStar_All.pipe_left (fun _139_2261 -> Some (_139_2261)) _139_2262))
in (push_free_var env lid vname _139_2263))
in ((FStar_List.append decls2 ((tok_typing)::[])), _139_2264))
end
| _50_3286 -> begin
(
# 1953 "FStar.ToSMT.Encode.fst"
let vtok_decl = FStar_ToSMT_Term.DeclFun ((vtok, [], FStar_ToSMT_Term.Term_sort, None))
in (
# 1954 "FStar.ToSMT.Encode.fst"
let vtok_fresh = (let _139_2265 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (vtok, FStar_ToSMT_Term.Term_sort) _139_2265))
in (
# 1955 "FStar.ToSMT.Encode.fst"
let name_tok_corr = (let _139_2269 = (let _139_2268 = (let _139_2267 = (let _139_2266 = (FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _139_2266))
in (FStar_ToSMT_Term.mkForall _139_2267))
in (_139_2268, None))
in FStar_ToSMT_Term.Assume (_139_2269))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_50_3292) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_50_3295) with
| (decls2, env) -> begin
(
# 1958 "FStar.ToSMT.Encode.fst"
let _50_3303 = (
# 1959 "FStar.ToSMT.Encode.fst"
let res_t = (FStar_Absyn_Util.compress_typ res_t)
in (
# 1960 "FStar.ToSMT.Encode.fst"
let _50_3299 = (encode_typ_term res_t env')
in (match (_50_3299) with
| (encoded_res_t, decls) -> begin
(let _139_2270 = (FStar_ToSMT_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _139_2270, decls))
end)))
in (match (_50_3303) with
| (encoded_res_t, ty_pred, decls3) -> begin
(
# 1962 "FStar.ToSMT.Encode.fst"
let typingAx = (let _139_2274 = (let _139_2273 = (let _139_2272 = (let _139_2271 = (FStar_ToSMT_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _139_2271))
in (FStar_ToSMT_Term.mkForall _139_2272))
in (_139_2273, Some ("free var typing")))
in FStar_ToSMT_Term.Assume (_139_2274))
in (
# 1963 "FStar.ToSMT.Encode.fst"
let g = (let _139_2276 = (let _139_2275 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_139_2275)
in (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) _139_2276))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end
end)
and encode_signature : env_t  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _50_3310 se -> (match (_50_3310) with
| (g, env) -> begin
(
# 1969 "FStar.ToSMT.Encode.fst"
let _50_3314 = (encode_sigelt env se)
in (match (_50_3314) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

# 1972 "FStar.ToSMT.Encode.fst"
let encode_env_bindings : env_t  ->  FStar_Tc_Env.binding Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env bindings -> (
# 1997 "FStar.ToSMT.Encode.fst"
let encode_binding = (fun b _50_3321 -> (match (_50_3321) with
| (decls, env) -> begin
(match (b) with
| FStar_Tc_Env.Binding_var (x, t0) -> begin
(
# 1999 "FStar.ToSMT.Encode.fst"
let _50_3329 = (new_term_constant env x)
in (match (_50_3329) with
| (xxsym, xx, env') -> begin
(
# 2000 "FStar.ToSMT.Encode.fst"
let t1 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (
# 2001 "FStar.ToSMT.Encode.fst"
let _50_3331 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _139_2291 = (FStar_Absyn_Print.strBvd x)
in (let _139_2290 = (FStar_Absyn_Print.typ_to_string t0)
in (let _139_2289 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _139_2291 _139_2290 _139_2289))))
end else begin
()
end
in (
# 2003 "FStar.ToSMT.Encode.fst"
let _50_3335 = (encode_typ_pred None t1 env xx)
in (match (_50_3335) with
| (t, decls') -> begin
(
# 2004 "FStar.ToSMT.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _139_2295 = (let _139_2294 = (FStar_Absyn_Print.strBvd x)
in (let _139_2293 = (FStar_Absyn_Print.typ_to_string t0)
in (let _139_2292 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _139_2294 _139_2293 _139_2292))))
in Some (_139_2295))
end else begin
None
end
in (
# 2008 "FStar.ToSMT.Encode.fst"
let g = (FStar_List.append (FStar_List.append ((FStar_ToSMT_Term.DeclFun ((xxsym, [], FStar_ToSMT_Term.Term_sort, caption)))::[]) decls') ((FStar_ToSMT_Term.Assume ((t, None)))::[]))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(
# 2013 "FStar.ToSMT.Encode.fst"
let _50_3345 = (new_typ_constant env a)
in (match (_50_3345) with
| (aasym, aa, env') -> begin
(
# 2014 "FStar.ToSMT.Encode.fst"
let _50_3348 = (encode_knd k env aa)
in (match (_50_3348) with
| (k, decls') -> begin
(
# 2015 "FStar.ToSMT.Encode.fst"
let g = (let _139_2301 = (let _139_2300 = (let _139_2299 = (let _139_2298 = (let _139_2297 = (let _139_2296 = (FStar_Absyn_Print.strBvd a)
in Some (_139_2296))
in (aasym, [], FStar_ToSMT_Term.Type_sort, _139_2297))
in FStar_ToSMT_Term.DeclFun (_139_2298))
in (_139_2299)::[])
in (FStar_List.append _139_2300 decls'))
in (FStar_List.append _139_2301 ((FStar_ToSMT_Term.Assume ((k, None)))::[])))
in ((FStar_List.append decls g), env'))
end))
end))
end
| FStar_Tc_Env.Binding_lid (x, t) -> begin
(
# 2020 "FStar.ToSMT.Encode.fst"
let t_norm = (whnf env t)
in (
# 2021 "FStar.ToSMT.Encode.fst"
let _50_3357 = (encode_free_var env x t t_norm [])
in (match (_50_3357) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end)))
end
| FStar_Tc_Env.Binding_sig (se) -> begin
(
# 2024 "FStar.ToSMT.Encode.fst"
let _50_3362 = (encode_sigelt env se)
in (match (_50_3362) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

# 2028 "FStar.ToSMT.Encode.fst"
let encode_labels = (fun labs -> (
# 2029 "FStar.ToSMT.Encode.fst"
let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _50_3369 -> (match (_50_3369) with
| (l, _50_3366, _50_3368) -> begin
FStar_ToSMT_Term.DeclFun (((Prims.fst l), [], FStar_ToSMT_Term.Bool_sort, None))
end))))
in (
# 2030 "FStar.ToSMT.Encode.fst"
let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _50_3376 -> (match (_50_3376) with
| (l, _50_3373, _50_3375) -> begin
(let _139_2309 = (FStar_All.pipe_left (fun _139_2305 -> FStar_ToSMT_Term.Echo (_139_2305)) (Prims.fst l))
in (let _139_2308 = (let _139_2307 = (let _139_2306 = (FStar_ToSMT_Term.mkFreeV l)
in FStar_ToSMT_Term.Eval (_139_2306))
in (_139_2307)::[])
in (_139_2309)::_139_2308))
end))))
in (prefix, suffix))))

# 2035 "FStar.ToSMT.Encode.fst"
let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 2036 "FStar.ToSMT.Encode.fst"
let init_env : FStar_Tc_Env.env  ->  Prims.unit = (fun tcenv -> (let _139_2314 = (let _139_2313 = (let _139_2312 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _139_2312; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_139_2313)::[])
in (FStar_ST.op_Colon_Equals last_env _139_2314)))

# 2039 "FStar.ToSMT.Encode.fst"
let get_env : FStar_Tc_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_50_3382 -> begin
(
# 2041 "FStar.ToSMT.Encode.fst"
let _50_3385 = e
in {bindings = _50_3385.bindings; depth = _50_3385.depth; tcenv = tcenv; warn = _50_3385.warn; cache = _50_3385.cache; nolabels = _50_3385.nolabels; use_zfuel_name = _50_3385.use_zfuel_name; encode_non_total_function_typ = _50_3385.encode_non_total_function_typ})
end))

# 2042 "FStar.ToSMT.Encode.fst"
let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _50_3391::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

# 2045 "FStar.ToSMT.Encode.fst"
let push_env : Prims.unit  ->  Prims.unit = (fun _50_3393 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(
# 2048 "FStar.ToSMT.Encode.fst"
let refs = (FStar_Util.smap_copy hd.cache)
in (
# 2049 "FStar.ToSMT.Encode.fst"
let top = (
# 2049 "FStar.ToSMT.Encode.fst"
let _50_3399 = hd
in {bindings = _50_3399.bindings; depth = _50_3399.depth; tcenv = _50_3399.tcenv; warn = _50_3399.warn; cache = refs; nolabels = _50_3399.nolabels; use_zfuel_name = _50_3399.use_zfuel_name; encode_non_total_function_typ = _50_3399.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

# 2051 "FStar.ToSMT.Encode.fst"
let pop_env : Prims.unit  ->  Prims.unit = (fun _50_3402 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _50_3406::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

# 2054 "FStar.ToSMT.Encode.fst"
let mark_env : Prims.unit  ->  Prims.unit = (fun _50_3408 -> (match (()) with
| () -> begin
(push_env ())
end))

# 2055 "FStar.ToSMT.Encode.fst"
let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _50_3409 -> (match (()) with
| () -> begin
(pop_env ())
end))

# 2056 "FStar.ToSMT.Encode.fst"
let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _50_3410 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_50_3413::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _50_3418 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 2062 "FStar.ToSMT.Encode.fst"
let init : FStar_Tc_Env.env  ->  Prims.unit = (fun tcenv -> (
# 2063 "FStar.ToSMT.Encode.fst"
let _50_3420 = (init_env tcenv)
in (
# 2064 "FStar.ToSMT.Encode.fst"
let _50_3422 = (FStar_ToSMT_Z3.init ())
in (FStar_ToSMT_Z3.giveZ3 ((FStar_ToSMT_Term.DefPrelude)::[])))))

# 2066 "FStar.ToSMT.Encode.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 2067 "FStar.ToSMT.Encode.fst"
let _50_3425 = (push_env ())
in (
# 2068 "FStar.ToSMT.Encode.fst"
let _50_3427 = (varops.push ())
in (FStar_ToSMT_Z3.push msg))))

# 2070 "FStar.ToSMT.Encode.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 2071 "FStar.ToSMT.Encode.fst"
let _50_3430 = (let _139_2335 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _139_2335))
in (
# 2072 "FStar.ToSMT.Encode.fst"
let _50_3432 = (varops.pop ())
in (FStar_ToSMT_Z3.pop msg))))

# 2074 "FStar.ToSMT.Encode.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 2075 "FStar.ToSMT.Encode.fst"
let _50_3435 = (mark_env ())
in (
# 2076 "FStar.ToSMT.Encode.fst"
let _50_3437 = (varops.mark ())
in (FStar_ToSMT_Z3.mark msg))))

# 2078 "FStar.ToSMT.Encode.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 2079 "FStar.ToSMT.Encode.fst"
let _50_3440 = (reset_mark_env ())
in (
# 2080 "FStar.ToSMT.Encode.fst"
let _50_3442 = (varops.reset_mark ())
in (FStar_ToSMT_Z3.reset_mark msg))))

# 2082 "FStar.ToSMT.Encode.fst"
let commit_mark = (fun msg -> (
# 2083 "FStar.ToSMT.Encode.fst"
let _50_3445 = (commit_mark_env ())
in (
# 2084 "FStar.ToSMT.Encode.fst"
let _50_3447 = (varops.commit_mark ())
in (FStar_ToSMT_Z3.commit_mark msg))))

# 2086 "FStar.ToSMT.Encode.fst"
let encode_sig : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (
# 2087 "FStar.ToSMT.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _139_2349 = (let _139_2348 = (let _139_2347 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (Prims.strcat "encoding sigelt " _139_2347))
in FStar_ToSMT_Term.Caption (_139_2348))
in (_139_2349)::decls)
end else begin
decls
end)
in (
# 2091 "FStar.ToSMT.Encode.fst"
let env = (get_env tcenv)
in (
# 2092 "FStar.ToSMT.Encode.fst"
let _50_3456 = (encode_sigelt env se)
in (match (_50_3456) with
| (decls, env) -> begin
(
# 2093 "FStar.ToSMT.Encode.fst"
let _50_3457 = (set_env env)
in (let _139_2350 = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 _139_2350)))
end)))))

# 2096 "FStar.ToSMT.Encode.fst"
let encode_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (
# 2097 "FStar.ToSMT.Encode.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Ident.str)
in (
# 2098 "FStar.ToSMT.Encode.fst"
let _50_3462 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _139_2355 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Absyn_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "Encoding externals for %s ... %s exports\n" name _139_2355))
end else begin
()
end
in (
# 2100 "FStar.ToSMT.Encode.fst"
let env = (get_env tcenv)
in (
# 2101 "FStar.ToSMT.Encode.fst"
let _50_3469 = (encode_signature (
# 2101 "FStar.ToSMT.Encode.fst"
let _50_3465 = env
in {bindings = _50_3465.bindings; depth = _50_3465.depth; tcenv = _50_3465.tcenv; warn = false; cache = _50_3465.cache; nolabels = _50_3465.nolabels; use_zfuel_name = _50_3465.use_zfuel_name; encode_non_total_function_typ = _50_3465.encode_non_total_function_typ}) modul.FStar_Absyn_Syntax.exports)
in (match (_50_3469) with
| (decls, env) -> begin
(
# 2102 "FStar.ToSMT.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(
# 2104 "FStar.ToSMT.Encode.fst"
let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::decls) ((FStar_ToSMT_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (
# 2107 "FStar.ToSMT.Encode.fst"
let _50_3475 = (set_env (
# 2107 "FStar.ToSMT.Encode.fst"
let _50_3473 = env
in {bindings = _50_3473.bindings; depth = _50_3473.depth; tcenv = _50_3473.tcenv; warn = true; cache = _50_3473.cache; nolabels = _50_3473.nolabels; use_zfuel_name = _50_3473.use_zfuel_name; encode_non_total_function_typ = _50_3473.encode_non_total_function_typ}))
in (
# 2108 "FStar.ToSMT.Encode.fst"
let _50_3477 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (
# 2109 "FStar.ToSMT.Encode.fst"
let decls = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

# 2112 "FStar.ToSMT.Encode.fst"
let solve : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun tcenv q -> (
# 2113 "FStar.ToSMT.Encode.fst"
let _50_3482 = (let _139_2364 = (let _139_2363 = (let _139_2362 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _139_2362))
in (FStar_Util.format1 "Starting query at %s" _139_2363))
in (push _139_2364))
in (
# 2114 "FStar.ToSMT.Encode.fst"
let pop = (fun _50_3485 -> (match (()) with
| () -> begin
(let _139_2369 = (let _139_2368 = (let _139_2367 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _139_2367))
in (FStar_Util.format1 "Ending query at %s" _139_2368))
in (pop _139_2369))
end))
in (
# 2115 "FStar.ToSMT.Encode.fst"
let _50_3544 = (
# 2116 "FStar.ToSMT.Encode.fst"
let env = (get_env tcenv)
in (
# 2117 "FStar.ToSMT.Encode.fst"
let bindings = (FStar_Tc_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (
# 2118 "FStar.ToSMT.Encode.fst"
let _50_3518 = (
# 2119 "FStar.ToSMT.Encode.fst"
let rec aux = (fun bindings -> (match (bindings) with
| FStar_Tc_Env.Binding_var (x, t)::rest -> begin
(
# 2121 "FStar.ToSMT.Encode.fst"
let _50_3500 = (aux rest)
in (match (_50_3500) with
| (out, rest) -> begin
(
# 2122 "FStar.ToSMT.Encode.fst"
let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
in (let _139_2375 = (let _139_2374 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_139_2374)::out)
in (_139_2375, rest)))
end))
end
| FStar_Tc_Env.Binding_typ (a, k)::rest -> begin
(
# 2125 "FStar.ToSMT.Encode.fst"
let _50_3510 = (aux rest)
in (match (_50_3510) with
| (out, rest) -> begin
(let _139_2377 = (let _139_2376 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_139_2376)::out)
in (_139_2377, rest))
end))
end
| _50_3512 -> begin
([], bindings)
end))
in (
# 2128 "FStar.ToSMT.Encode.fst"
let _50_3515 = (aux bindings)
in (match (_50_3515) with
| (closing, bindings) -> begin
(let _139_2378 = (FStar_Absyn_Util.close_forall (FStar_List.rev closing) q)
in (_139_2378, bindings))
end)))
in (match (_50_3518) with
| (q, bindings) -> begin
(
# 2130 "FStar.ToSMT.Encode.fst"
let _50_3527 = (let _139_2380 = (FStar_List.filter (fun _50_32 -> (match (_50_32) with
| FStar_Tc_Env.Binding_sig (_50_3521) -> begin
false
end
| _50_3524 -> begin
true
end)) bindings)
in (encode_env_bindings env _139_2380))
in (match (_50_3527) with
| (env_decls, env) -> begin
(
# 2131 "FStar.ToSMT.Encode.fst"
let _50_3528 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _139_2381 = (FStar_Absyn_Print.formula_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _139_2381))
end else begin
()
end
in (
# 2132 "FStar.ToSMT.Encode.fst"
let _50_3533 = (encode_formula_with_labels q env)
in (match (_50_3533) with
| (phi, labels, qdecls) -> begin
(
# 2133 "FStar.ToSMT.Encode.fst"
let _50_3536 = (encode_labels labels)
in (match (_50_3536) with
| (label_prefix, label_suffix) -> begin
(
# 2134 "FStar.ToSMT.Encode.fst"
let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (
# 2138 "FStar.ToSMT.Encode.fst"
let qry = (let _139_2383 = (let _139_2382 = (FStar_ToSMT_Term.mkNot phi)
in (_139_2382, Some ("query")))
in FStar_ToSMT_Term.Assume (_139_2383))
in (
# 2139 "FStar.ToSMT.Encode.fst"
let suffix = (FStar_List.append label_suffix ((FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))
end))))
in (match (_50_3544) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_ToSMT_Term.Assume ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (FStar_ToSMT_Term.False, _50_3551); FStar_ToSMT_Term.hash = _50_3548; FStar_ToSMT_Term.freevars = _50_3546}, _50_3556) -> begin
(
# 2142 "FStar.ToSMT.Encode.fst"
let _50_3559 = (pop ())
in ())
end
| _50_3562 when tcenv.FStar_Tc_Env.admit -> begin
(
# 2143 "FStar.ToSMT.Encode.fst"
let _50_3563 = (pop ())
in ())
end
| FStar_ToSMT_Term.Assume (q, _50_3567) -> begin
(
# 2145 "FStar.ToSMT.Encode.fst"
let fresh = ((FStar_String.length q.FStar_ToSMT_Term.hash) >= 2048)
in (
# 2146 "FStar.ToSMT.Encode.fst"
let _50_3571 = (FStar_ToSMT_Z3.giveZ3 prefix)
in (
# 2148 "FStar.ToSMT.Encode.fst"
let with_fuel = (fun p _50_3577 -> (match (_50_3577) with
| (n, i) -> begin
(let _139_2406 = (let _139_2405 = (let _139_2390 = (let _139_2389 = (FStar_Util.string_of_int n)
in (let _139_2388 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _139_2389 _139_2388)))
in FStar_ToSMT_Term.Caption (_139_2390))
in (let _139_2404 = (let _139_2403 = (let _139_2395 = (let _139_2394 = (let _139_2393 = (let _139_2392 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _139_2391 = (FStar_ToSMT_Term.n_fuel n)
in (_139_2392, _139_2391)))
in (FStar_ToSMT_Term.mkEq _139_2393))
in (_139_2394, None))
in FStar_ToSMT_Term.Assume (_139_2395))
in (let _139_2402 = (let _139_2401 = (let _139_2400 = (let _139_2399 = (let _139_2398 = (let _139_2397 = (FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _139_2396 = (FStar_ToSMT_Term.n_fuel i)
in (_139_2397, _139_2396)))
in (FStar_ToSMT_Term.mkEq _139_2398))
in (_139_2399, None))
in FStar_ToSMT_Term.Assume (_139_2400))
in (_139_2401)::(p)::(FStar_ToSMT_Term.CheckSat)::[])
in (_139_2403)::_139_2402))
in (_139_2405)::_139_2404))
in (FStar_List.append _139_2406 suffix))
end))
in (
# 2155 "FStar.ToSMT.Encode.fst"
let check = (fun p -> (
# 2156 "FStar.ToSMT.Encode.fst"
let initial_config = (let _139_2410 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _139_2409 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_139_2410, _139_2409)))
in (
# 2157 "FStar.ToSMT.Encode.fst"
let alt_configs = (let _139_2429 = (let _139_2428 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _139_2413 = (let _139_2412 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _139_2411 = (FStar_ST.read FStar_Options.max_ifuel)
in (_139_2412, _139_2411)))
in (_139_2413)::[])
end else begin
[]
end
in (let _139_2427 = (let _139_2426 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _139_2416 = (let _139_2415 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _139_2414 = (FStar_ST.read FStar_Options.max_ifuel)
in (_139_2415, _139_2414)))
in (_139_2416)::[])
end else begin
[]
end
in (let _139_2425 = (let _139_2424 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _139_2419 = (let _139_2418 = (FStar_ST.read FStar_Options.max_fuel)
in (let _139_2417 = (FStar_ST.read FStar_Options.max_ifuel)
in (_139_2418, _139_2417)))
in (_139_2419)::[])
end else begin
[]
end
in (let _139_2423 = (let _139_2422 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _139_2421 = (let _139_2420 = (FStar_ST.read FStar_Options.min_fuel)
in (_139_2420, 1))
in (_139_2421)::[])
end else begin
[]
end
in (_139_2422)::[])
in (_139_2424)::_139_2423))
in (_139_2426)::_139_2425))
in (_139_2428)::_139_2427))
in (FStar_List.flatten _139_2429))
in (
# 2162 "FStar.ToSMT.Encode.fst"
let report = (fun errs -> (
# 2163 "FStar.ToSMT.Encode.fst"
let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Absyn_Syntax.dummyRange))::[]
end
| _50_3586 -> begin
errs
end)
in (
# 2166 "FStar.ToSMT.Encode.fst"
let _50_3588 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _139_2437 = (let _139_2432 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _139_2432))
in (let _139_2436 = (let _139_2433 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _139_2433 FStar_Util.string_of_int))
in (let _139_2435 = (let _139_2434 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _139_2434 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _139_2437 _139_2436 _139_2435))))
end else begin
()
end
in (FStar_Tc_Errors.add_errors tcenv errs))))
in (
# 2173 "FStar.ToSMT.Encode.fst"
let rec try_alt_configs = (fun p errs _50_33 -> (match (_50_33) with
| [] -> begin
(report errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _139_2448 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _139_2448 (cb mi p [])))
end
| _50_3600 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _139_2450 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _139_2450 (fun _50_3606 -> (match (_50_3606) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _50_3609 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _50_3612 p alt _50_3617 -> (match ((_50_3612, _50_3617)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _139_2458 = (let _139_2455 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _139_2455))
in (let _139_2457 = (FStar_Util.string_of_int prev_fuel)
in (let _139_2456 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _139_2458 _139_2457 _139_2456))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _139_2459 = (with_fuel p initial_config)
in (FStar_ToSMT_Z3.ask fresh labels _139_2459 (cb initial_config p alt_configs))))))))
in (
# 2198 "FStar.ToSMT.Encode.fst"
let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 2200 "FStar.ToSMT.Encode.fst"
let _50_3622 = (let _139_2465 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_ToSMT_SplitQueryCases.can_handle_query _139_2465 q))
in (match (_50_3622) with
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
# 2205 "FStar.ToSMT.Encode.fst"
let _50_3623 = if (FStar_ST.read FStar_Options.admit_smt_queries) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end)
end)))))

# 2209 "FStar.ToSMT.Encode.fst"
let is_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (
# 2210 "FStar.ToSMT.Encode.fst"
let env = (get_env tcenv)
in (
# 2211 "FStar.ToSMT.Encode.fst"
let _50_3628 = (push "query")
in (
# 2212 "FStar.ToSMT.Encode.fst"
let _50_3635 = (encode_formula_with_labels q env)
in (match (_50_3635) with
| (f, _50_3632, _50_3634) -> begin
(
# 2213 "FStar.ToSMT.Encode.fst"
let _50_3636 = (pop "query")
in (match (f.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _50_3640) -> begin
true
end
| _50_3644 -> begin
false
end))
end)))))

# 2218 "FStar.ToSMT.Encode.fst"
let solver : FStar_Tc_Env.solver_t = {FStar_Tc_Env.init = init; FStar_Tc_Env.push = push; FStar_Tc_Env.pop = pop; FStar_Tc_Env.mark = mark; FStar_Tc_Env.reset_mark = reset_mark; FStar_Tc_Env.commit_mark = commit_mark; FStar_Tc_Env.encode_modul = encode_modul; FStar_Tc_Env.encode_sig = encode_sig; FStar_Tc_Env.solve = solve; FStar_Tc_Env.is_trivial = is_trivial; FStar_Tc_Env.finish = FStar_ToSMT_Z3.finish; FStar_Tc_Env.refresh = FStar_ToSMT_Z3.refresh}

# 2232 "FStar.ToSMT.Encode.fst"
let dummy : FStar_Tc_Env.solver_t = {FStar_Tc_Env.init = (fun _50_3645 -> ()); FStar_Tc_Env.push = (fun _50_3647 -> ()); FStar_Tc_Env.pop = (fun _50_3649 -> ()); FStar_Tc_Env.mark = (fun _50_3651 -> ()); FStar_Tc_Env.reset_mark = (fun _50_3653 -> ()); FStar_Tc_Env.commit_mark = (fun _50_3655 -> ()); FStar_Tc_Env.encode_modul = (fun _50_3657 _50_3659 -> ()); FStar_Tc_Env.encode_sig = (fun _50_3661 _50_3663 -> ()); FStar_Tc_Env.solve = (fun _50_3665 _50_3667 -> ()); FStar_Tc_Env.is_trivial = (fun _50_3669 _50_3671 -> false); FStar_Tc_Env.finish = (fun _50_3673 -> ()); FStar_Tc_Env.refresh = (fun _50_3674 -> ())}





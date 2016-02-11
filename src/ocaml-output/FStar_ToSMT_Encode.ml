
open Prims
# 31 "FStar.ToSMT.Encode.fst"
let add_fuel = (fun x tl -> if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
tl
end else begin
(x)::tl
end)

# 32 "FStar.ToSMT.Encode.fst"
let withenv = (fun c _47_39 -> (match (_47_39) with
| (a, b) -> begin
(a, b, c)
end))

# 33 "FStar.ToSMT.Encode.fst"
let vargs = (fun args -> (FStar_List.filter (fun _47_1 -> (match (_47_1) with
| (FStar_Util.Inl (_47_43), _47_46) -> begin
false
end
| _47_49 -> begin
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
let mk_typ_projector_name : FStar_Ident.lident  ->  FStar_Absyn_Syntax.btvdef  ->  Prims.string = (fun lid a -> (let _126_14 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (escape_null_name a))
in (FStar_All.pipe_left escape _126_14)))

# 45 "FStar.ToSMT.Encode.fst"
let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Absyn_Syntax.bvvdef  ->  Prims.string = (fun lid a -> (
# 46 "FStar.ToSMT.Encode.fst"
let a = (let _126_19 = (FStar_Absyn_Util.unmangle_field_name a.FStar_Absyn_Syntax.ppname)
in {FStar_Absyn_Syntax.ppname = _126_19; FStar_Absyn_Syntax.realname = a.FStar_Absyn_Syntax.realname})
in (let _126_20 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (escape_null_name a))
in (FStar_All.pipe_left escape _126_20))))

# 48 "FStar.ToSMT.Encode.fst"
let primitive_projector_by_pos : FStar_Tc_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (
# 49 "FStar.ToSMT.Encode.fst"
let fail = (fun _47_61 -> (match (()) with
| () -> begin
(let _126_30 = (let _126_29 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" _126_29 lid.FStar_Ident.str))
in (FStar_All.failwith _126_30))
end))
in (
# 50 "FStar.ToSMT.Encode.fst"
let t = (FStar_Tc_Env.lookup_datacon env lid)
in (match ((let _126_31 = (FStar_Absyn_Util.compress_typ t)
in _126_31.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, _47_65) -> begin
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
| _47_74 -> begin
(fail ())
end))))

# 61 "FStar.ToSMT.Encode.fst"
let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (let _126_37 = (let _126_36 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str _126_36))
in (FStar_All.pipe_left escape _126_37)))

# 62 "FStar.ToSMT.Encode.fst"
let mk_typ_projector : FStar_Ident.lident  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_ToSMT_Term.term = (fun lid a -> (let _126_43 = (let _126_42 = (mk_typ_projector_name lid a)
in (_126_42, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Type_sort))))
in (FStar_ToSMT_Term.mkFreeV _126_43)))

# 64 "FStar.ToSMT.Encode.fst"
let mk_term_projector : FStar_Ident.lident  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_ToSMT_Term.term = (fun lid a -> (let _126_49 = (let _126_48 = (mk_term_projector_name lid a)
in (_126_48, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _126_49)))

# 66 "FStar.ToSMT.Encode.fst"
let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_ToSMT_Term.term = (fun lid i -> (let _126_55 = (let _126_54 = (mk_term_projector_name_by_pos lid i)
in (_126_54, FStar_ToSMT_Term.Arrow ((FStar_ToSMT_Term.Term_sort, FStar_ToSMT_Term.Term_sort))))
in (FStar_ToSMT_Term.mkFreeV _126_55)))

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
let new_scope = (fun _47_100 -> (match (()) with
| () -> begin
(let _126_159 = (FStar_Util.smap_create 100)
in (let _126_158 = (FStar_Util.smap_create 100)
in (_126_159, _126_158)))
end))
in (
# 87 "FStar.ToSMT.Encode.fst"
let scopes = (let _126_161 = (let _126_160 = (new_scope ())
in (_126_160)::[])
in (FStar_Util.mk_ref _126_161))
in (
# 88 "FStar.ToSMT.Encode.fst"
let mk_unique = (fun y -> (
# 89 "FStar.ToSMT.Encode.fst"
let y = (escape y)
in (
# 90 "FStar.ToSMT.Encode.fst"
let y = (match ((let _126_165 = (FStar_ST.read scopes)
in (FStar_Util.find_map _126_165 (fun _47_108 -> (match (_47_108) with
| (names, _47_107) -> begin
(FStar_Util.smap_try_find names y)
end))))) with
| None -> begin
y
end
| Some (_47_111) -> begin
(
# 92 "FStar.ToSMT.Encode.fst"
let _47_113 = (FStar_Util.incr ctr)
in (let _126_167 = (let _126_166 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _126_166))
in (Prims.strcat (Prims.strcat y "__") _126_167)))
end)
in (
# 93 "FStar.ToSMT.Encode.fst"
let top_scope = (let _126_169 = (let _126_168 = (FStar_ST.read scopes)
in (FStar_List.hd _126_168))
in (FStar_All.pipe_left Prims.fst _126_169))
in (
# 94 "FStar.ToSMT.Encode.fst"
let _47_117 = (FStar_Util.smap_add top_scope y true)
in y)))))
in (
# 95 "FStar.ToSMT.Encode.fst"
let new_var = (fun pp rn -> (let _126_175 = (let _126_174 = (FStar_All.pipe_left mk_unique pp.FStar_Ident.idText)
in (Prims.strcat _126_174 "__"))
in (Prims.strcat _126_175 rn.FStar_Ident.idText)))
in (
# 96 "FStar.ToSMT.Encode.fst"
let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (
# 97 "FStar.ToSMT.Encode.fst"
let next_id = (fun _47_125 -> (match (()) with
| () -> begin
(
# 97 "FStar.ToSMT.Encode.fst"
let _47_126 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end))
in (
# 98 "FStar.ToSMT.Encode.fst"
let fresh = (fun pfx -> (let _126_183 = (let _126_182 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _126_182))
in (FStar_Util.format2 "%s_%s" pfx _126_183)))
in (
# 99 "FStar.ToSMT.Encode.fst"
let string_const = (fun s -> (match ((let _126_187 = (FStar_ST.read scopes)
in (FStar_Util.find_map _126_187 (fun _47_135 -> (match (_47_135) with
| (_47_133, strings) -> begin
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
let f = (let _126_188 = (FStar_ToSMT_Term.mk_String_const id)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxString _126_188))
in (
# 104 "FStar.ToSMT.Encode.fst"
let top_scope = (let _126_190 = (let _126_189 = (FStar_ST.read scopes)
in (FStar_List.hd _126_189))
in (FStar_All.pipe_left Prims.snd _126_190))
in (
# 105 "FStar.ToSMT.Encode.fst"
let _47_142 = (FStar_Util.smap_add top_scope s f)
in f))))
end))
in (
# 107 "FStar.ToSMT.Encode.fst"
let push = (fun _47_145 -> (match (()) with
| () -> begin
(let _126_195 = (let _126_194 = (new_scope ())
in (let _126_193 = (FStar_ST.read scopes)
in (_126_194)::_126_193))
in (FStar_ST.op_Colon_Equals scopes _126_195))
end))
in (
# 108 "FStar.ToSMT.Encode.fst"
let pop = (fun _47_147 -> (match (()) with
| () -> begin
(let _126_199 = (let _126_198 = (FStar_ST.read scopes)
in (FStar_List.tl _126_198))
in (FStar_ST.op_Colon_Equals scopes _126_199))
end))
in (
# 109 "FStar.ToSMT.Encode.fst"
let mark = (fun _47_149 -> (match (()) with
| () -> begin
(push ())
end))
in (
# 110 "FStar.ToSMT.Encode.fst"
let reset_mark = (fun _47_151 -> (match (()) with
| () -> begin
(pop ())
end))
in (
# 111 "FStar.ToSMT.Encode.fst"
let commit_mark = (fun _47_153 -> (match (()) with
| () -> begin
(match ((FStar_ST.read scopes)) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(
# 113 "FStar.ToSMT.Encode.fst"
let _47_166 = (FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ())
in (
# 114 "FStar.ToSMT.Encode.fst"
let _47_171 = (FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ())
in (FStar_ST.op_Colon_Equals scopes (((next1, next2))::tl))))
end
| _47_174 -> begin
(FStar_All.failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

# 128 "FStar.ToSMT.Encode.fst"
let unmangle = (fun x -> (let _126_215 = (let _126_214 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.ppname)
in (let _126_213 = (FStar_Absyn_Util.unmangle_field_name x.FStar_Absyn_Syntax.realname)
in (_126_214, _126_213)))
in (FStar_Absyn_Util.mkbvd _126_215)))

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
let ___Binding_var____0 : binding  ->  (FStar_Absyn_Syntax.bvvdef * FStar_ToSMT_Term.term) = (fun projectee -> (match (projectee) with
| Binding_var (_47_179) -> begin
_47_179
end))

# 134 "FStar.ToSMT.Encode.fst"
let ___Binding_tvar____0 : binding  ->  (FStar_Absyn_Syntax.btvdef * FStar_ToSMT_Term.term) = (fun projectee -> (match (projectee) with
| Binding_tvar (_47_182) -> begin
_47_182
end))

# 135 "FStar.ToSMT.Encode.fst"
let ___Binding_fvar____0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_47_185) -> begin
_47_185
end))

# 136 "FStar.ToSMT.Encode.fst"
let ___Binding_ftvar____0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_ToSMT_Term.term Prims.option) = (fun projectee -> (match (projectee) with
| Binding_ftvar (_47_188) -> begin
_47_188
end))

# 138 "FStar.ToSMT.Encode.fst"
let binder_of_eithervar = (fun v -> (v, None))

# 139 "FStar.ToSMT.Encode.fst"
type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_Tc_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_ToSMT_Term.sort Prims.list * FStar_ToSMT_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}

# 139 "FStar.ToSMT.Encode.fst"
let is_Mkenv_t : env_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkenv_t"))))

# 149 "FStar.ToSMT.Encode.fst"
let print_env : env_t  ->  Prims.string = (fun e -> (let _126_301 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun _47_2 -> (match (_47_2) with
| Binding_var (x, t) -> begin
(FStar_Absyn_Print.strBvd x)
end
| Binding_tvar (a, t) -> begin
(FStar_Absyn_Print.strBvd a)
end
| Binding_fvar (l, s, t, _47_213) -> begin
(FStar_Absyn_Print.sli l)
end
| Binding_ftvar (l, s, t) -> begin
(FStar_Absyn_Print.sli l)
end))))
in (FStar_All.pipe_right _126_301 (FStar_String.concat ", "))))

# 156 "FStar.ToSMT.Encode.fst"
let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))

# 158 "FStar.ToSMT.Encode.fst"
let caption_t : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  Prims.string Prims.option = (fun env t -> if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _126_311 = (FStar_Absyn_Print.typ_to_string t)
in Some (_126_311))
end else begin
None
end)

# 163 "FStar.ToSMT.Encode.fst"
let fresh_fvar : Prims.string  ->  FStar_ToSMT_Term.sort  ->  (Prims.string * FStar_ToSMT_Term.term) = (fun x s -> (
# 163 "FStar.ToSMT.Encode.fst"
let xsym = (varops.fresh x)
in (let _126_316 = (FStar_ToSMT_Term.mkFreeV (xsym, s))
in (xsym, _126_316))))

# 167 "FStar.ToSMT.Encode.fst"
let gen_term_var : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (
# 168 "FStar.ToSMT.Encode.fst"
let ysym = (let _126_321 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" _126_321))
in (
# 169 "FStar.ToSMT.Encode.fst"
let y = (FStar_ToSMT_Term.mkFreeV (ysym, FStar_ToSMT_Term.Term_sort))
in (ysym, y, (
# 170 "FStar.ToSMT.Encode.fst"
let _47_232 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _47_232.tcenv; warn = _47_232.warn; cache = _47_232.cache; nolabels = _47_232.nolabels; use_zfuel_name = _47_232.use_zfuel_name; encode_non_total_function_typ = _47_232.encode_non_total_function_typ})))))

# 171 "FStar.ToSMT.Encode.fst"
let new_term_constant : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (
# 172 "FStar.ToSMT.Encode.fst"
let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (
# 173 "FStar.ToSMT.Encode.fst"
let y = (FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (
# 174 "FStar.ToSMT.Encode.fst"
let _47_238 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _47_238.depth; tcenv = _47_238.tcenv; warn = _47_238.warn; cache = _47_238.cache; nolabels = _47_238.nolabels; use_zfuel_name = _47_238.use_zfuel_name; encode_non_total_function_typ = _47_238.encode_non_total_function_typ})))))

# 175 "FStar.ToSMT.Encode.fst"
let push_term_var : env_t  ->  FStar_Absyn_Syntax.bvvdef  ->  FStar_ToSMT_Term.term  ->  env_t = (fun env x t -> (
# 176 "FStar.ToSMT.Encode.fst"
let _47_243 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _47_243.depth; tcenv = _47_243.tcenv; warn = _47_243.warn; cache = _47_243.cache; nolabels = _47_243.nolabels; use_zfuel_name = _47_243.use_zfuel_name; encode_non_total_function_typ = _47_243.encode_non_total_function_typ}))

# 177 "FStar.ToSMT.Encode.fst"
let lookup_term_var = (fun env a -> (match ((lookup_binding env (fun _47_3 -> (match (_47_3) with
| Binding_var (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _47_253 -> begin
None
end)))) with
| None -> begin
(let _126_336 = (let _126_335 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound term variable not found: %s" _126_335))
in (FStar_All.failwith _126_336))
end
| Some (b, t) -> begin
t
end))

# 183 "FStar.ToSMT.Encode.fst"
let gen_typ_var : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (
# 184 "FStar.ToSMT.Encode.fst"
let ysym = (let _126_341 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@a" _126_341))
in (
# 185 "FStar.ToSMT.Encode.fst"
let y = (FStar_ToSMT_Term.mkFreeV (ysym, FStar_ToSMT_Term.Type_sort))
in (ysym, y, (
# 186 "FStar.ToSMT.Encode.fst"
let _47_263 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _47_263.tcenv; warn = _47_263.warn; cache = _47_263.cache; nolabels = _47_263.nolabels; use_zfuel_name = _47_263.use_zfuel_name; encode_non_total_function_typ = _47_263.encode_non_total_function_typ})))))

# 187 "FStar.ToSMT.Encode.fst"
let new_typ_constant : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  (Prims.string * FStar_ToSMT_Term.term * env_t) = (fun env x -> (
# 188 "FStar.ToSMT.Encode.fst"
let ysym = (varops.new_var x.FStar_Absyn_Syntax.ppname x.FStar_Absyn_Syntax.realname)
in (
# 189 "FStar.ToSMT.Encode.fst"
let y = (FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (
# 190 "FStar.ToSMT.Encode.fst"
let _47_269 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = _47_269.depth; tcenv = _47_269.tcenv; warn = _47_269.warn; cache = _47_269.cache; nolabels = _47_269.nolabels; use_zfuel_name = _47_269.use_zfuel_name; encode_non_total_function_typ = _47_269.encode_non_total_function_typ})))))

# 191 "FStar.ToSMT.Encode.fst"
let push_typ_var : env_t  ->  FStar_Absyn_Syntax.btvdef  ->  FStar_ToSMT_Term.term  ->  env_t = (fun env x t -> (
# 192 "FStar.ToSMT.Encode.fst"
let _47_274 = env
in {bindings = (Binding_tvar ((x, t)))::env.bindings; depth = _47_274.depth; tcenv = _47_274.tcenv; warn = _47_274.warn; cache = _47_274.cache; nolabels = _47_274.nolabels; use_zfuel_name = _47_274.use_zfuel_name; encode_non_total_function_typ = _47_274.encode_non_total_function_typ}))

# 193 "FStar.ToSMT.Encode.fst"
let lookup_typ_var = (fun env a -> (match ((lookup_binding env (fun _47_4 -> (match (_47_4) with
| Binding_tvar (b, t) when (FStar_Absyn_Util.bvd_eq b a.FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _47_284 -> begin
None
end)))) with
| None -> begin
(let _126_356 = (let _126_355 = (FStar_Absyn_Print.strBvd a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Bound type variable not found: %s" _126_355))
in (FStar_All.failwith _126_356))
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
in (let _126_367 = (
# 202 "FStar.ToSMT.Encode.fst"
let _47_294 = env
in (let _126_366 = (let _126_365 = (let _126_364 = (let _126_363 = (let _126_362 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _126_361 -> Some (_126_361)) _126_362))
in (x, fname, _126_363, None))
in Binding_fvar (_126_364))
in (_126_365)::env.bindings)
in {bindings = _126_366; depth = _47_294.depth; tcenv = _47_294.tcenv; warn = _47_294.warn; cache = _47_294.cache; nolabels = _47_294.nolabels; use_zfuel_name = _47_294.use_zfuel_name; encode_non_total_function_typ = _47_294.encode_non_total_function_typ}))
in (fname, ftok, _126_367)))))

# 203 "FStar.ToSMT.Encode.fst"
let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun _47_5 -> (match (_47_5) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _47_306 -> begin
None
end))))

# 205 "FStar.ToSMT.Encode.fst"
let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option * FStar_ToSMT_Term.term Prims.option) = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(let _126_378 = (let _126_377 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Name not found: %s" _126_377))
in (FStar_All.failwith _126_378))
end
| Some (s) -> begin
s
end))

# 209 "FStar.ToSMT.Encode.fst"
let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (
# 210 "FStar.ToSMT.Encode.fst"
let _47_316 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _47_316.depth; tcenv = _47_316.tcenv; warn = _47_316.warn; cache = _47_316.cache; nolabels = _47_316.nolabels; use_zfuel_name = _47_316.use_zfuel_name; encode_non_total_function_typ = _47_316.encode_non_total_function_typ}))

# 211 "FStar.ToSMT.Encode.fst"
let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (
# 212 "FStar.ToSMT.Encode.fst"
let _47_325 = (lookup_lid env x)
in (match (_47_325) with
| (t1, t2, _47_324) -> begin
(
# 213 "FStar.ToSMT.Encode.fst"
let t3 = (let _126_395 = (let _126_394 = (let _126_393 = (FStar_ToSMT_Term.mkApp ("ZFuel", []))
in (_126_393)::[])
in (f, _126_394))
in (FStar_ToSMT_Term.mkApp _126_395))
in (
# 214 "FStar.ToSMT.Encode.fst"
let _47_327 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _47_327.depth; tcenv = _47_327.tcenv; warn = _47_327.warn; cache = _47_327.cache; nolabels = _47_327.nolabels; use_zfuel_name = _47_327.use_zfuel_name; encode_non_total_function_typ = _47_327.encode_non_total_function_typ}))
end)))

# 215 "FStar.ToSMT.Encode.fst"
let lookup_free_var = (fun env a -> (
# 216 "FStar.ToSMT.Encode.fst"
let _47_334 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_47_334) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
f
end
| _47_338 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (_47_342, fuel::[]) -> begin
if (let _126_399 = (let _126_398 = (FStar_ToSMT_Term.fv_of_term fuel)
in (FStar_All.pipe_right _126_398 Prims.fst))
in (FStar_Util.starts_with _126_399 "fuel")) then begin
(let _126_400 = (FStar_ToSMT_Term.mkFreeV (name, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_ApplyEF _126_400 fuel))
end else begin
t
end
end
| _47_348 -> begin
t
end)
end
| _47_350 -> begin
(let _126_402 = (let _126_401 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" _126_401))
in (FStar_All.failwith _126_402))
end)
end)
end)))

# 230 "FStar.ToSMT.Encode.fst"
let lookup_free_var_name = (fun env a -> (
# 230 "FStar.ToSMT.Encode.fst"
let _47_358 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_47_358) with
| (x, _47_355, _47_357) -> begin
x
end)))

# 231 "FStar.ToSMT.Encode.fst"
let lookup_free_var_sym = (fun env a -> (
# 232 "FStar.ToSMT.Encode.fst"
let _47_364 = (lookup_lid env a.FStar_Absyn_Syntax.v)
in (match (_47_364) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (g, zf); FStar_ToSMT_Term.hash = _47_368; FStar_ToSMT_Term.freevars = _47_366}) when env.use_zfuel_name -> begin
(g, zf)
end
| _47_376 -> begin
(match (sym) with
| None -> begin
(FStar_ToSMT_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (g, fuel::[]) -> begin
(g, (fuel)::[])
end
| _47_386 -> begin
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
in (let _126_417 = (
# 247 "FStar.ToSMT.Encode.fst"
let _47_391 = env
in (let _126_416 = (let _126_415 = (let _126_414 = (let _126_413 = (let _126_412 = (FStar_ToSMT_Term.mkApp (ftok, []))
in (FStar_All.pipe_left (fun _126_411 -> Some (_126_411)) _126_412))
in (x, fname, _126_413))
in Binding_ftvar (_126_414))
in (_126_415)::env.bindings)
in {bindings = _126_416; depth = _47_391.depth; tcenv = _47_391.tcenv; warn = _47_391.warn; cache = _47_391.cache; nolabels = _47_391.nolabels; use_zfuel_name = _47_391.use_zfuel_name; encode_non_total_function_typ = _47_391.encode_non_total_function_typ}))
in (fname, ftok, _126_417)))))

# 248 "FStar.ToSMT.Encode.fst"
let lookup_tlid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_ToSMT_Term.term Prims.option) = (fun env a -> (match ((lookup_binding env (fun _47_6 -> (match (_47_6) with
| Binding_ftvar (b, t1, t2) when (FStar_Ident.lid_equals b a) -> begin
Some ((t1, t2))
end
| _47_402 -> begin
None
end)))) with
| None -> begin
(let _126_424 = (let _126_423 = (FStar_Absyn_Print.sli a)
in (FStar_Util.format1 "Type name not found: %s" _126_423))
in (FStar_All.failwith _126_424))
end
| Some (s) -> begin
s
end))

# 252 "FStar.ToSMT.Encode.fst"
let push_free_tvar : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (
# 253 "FStar.ToSMT.Encode.fst"
let _47_410 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _47_410.depth; tcenv = _47_410.tcenv; warn = _47_410.warn; cache = _47_410.cache; nolabels = _47_410.nolabels; use_zfuel_name = _47_410.use_zfuel_name; encode_non_total_function_typ = _47_410.encode_non_total_function_typ}))

# 254 "FStar.ToSMT.Encode.fst"
let lookup_free_tvar = (fun env a -> (match ((let _126_435 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _126_435 Prims.snd))) with
| None -> begin
(let _126_437 = (let _126_436 = (FStar_Absyn_Print.sli a.FStar_Absyn_Syntax.v)
in (FStar_Util.format1 "Type name not found: %s" _126_436))
in (FStar_All.failwith _126_437))
end
| Some (t) -> begin
t
end))

# 258 "FStar.ToSMT.Encode.fst"
let lookup_free_tvar_name = (fun env a -> (let _126_440 = (lookup_tlid env a.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _126_440 Prims.fst)))

# 260 "FStar.ToSMT.Encode.fst"
let tok_of_name : env_t  ->  Prims.string  ->  FStar_ToSMT_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun _47_7 -> (match (_47_7) with
| (Binding_fvar (_, nm', tok, _)) | (Binding_ftvar (_, nm', tok)) when (nm = nm') -> begin
tok
end
| _47_435 -> begin
None
end))))

# 270 "FStar.ToSMT.Encode.fst"
let mkForall_fuel' = (fun n _47_440 -> (match (_47_440) with
| (pats, vars, body) -> begin
(
# 271 "FStar.ToSMT.Encode.fst"
let fallback = (fun _47_442 -> (match (()) with
| () -> begin
(FStar_ToSMT_Term.mkForall (pats, vars, body))
end))
in if (FStar_ST.read FStar_Options.unthrottle_inductives) then begin
(fallback ())
end else begin
(
# 274 "FStar.ToSMT.Encode.fst"
let _47_445 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_47_445) with
| (fsym, fterm) -> begin
(
# 275 "FStar.ToSMT.Encode.fst"
let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var ("HasType"), args) -> begin
(FStar_ToSMT_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _47_455 -> begin
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
(let _126_453 = (add_fuel guards)
in (FStar_ToSMT_Term.mk_and_l _126_453))
end
| _47_468 -> begin
(let _126_454 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right _126_454 FStar_List.hd))
end)
in (FStar_ToSMT_Term.mkImp (guard, body')))
end
| _47_471 -> begin
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
(let _126_460 = (FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.FStar_Absyn_Syntax.v)
in (FStar_All.pipe_right _126_460 FStar_Option.isNone))
end
| _47_509 -> begin
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
let trivial_post : FStar_Absyn_Syntax.typ  ->  FStar_Absyn_Syntax.typ = (fun t -> (let _126_482 = (let _126_481 = (let _126_479 = (FStar_Absyn_Syntax.null_v_binder t)
in (_126_479)::[])
in (let _126_480 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.true_lid FStar_Absyn_Syntax.ktype)
in (_126_481, _126_480)))
in (FStar_Absyn_Syntax.mk_Typ_lam _126_482 None t.FStar_Absyn_Syntax.pos)))

# 313 "FStar.ToSMT.Encode.fst"
let mk_ApplyE : FStar_ToSMT_Term.term  ->  (Prims.string * FStar_ToSMT_Term.sort) Prims.list  ->  FStar_ToSMT_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_ToSMT_Term.Type_sort -> begin
(let _126_489 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyET out _126_489))
end
| FStar_ToSMT_Term.Fuel_sort -> begin
(let _126_490 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEF out _126_490))
end
| _47_526 -> begin
(let _126_491 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyEE out _126_491))
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
(let _126_504 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTT out _126_504))
end
| _47_541 -> begin
(let _126_505 = (FStar_ToSMT_Term.mkFreeV var)
in (FStar_ToSMT_Term.mk_ApplyTE out _126_505))
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
let is_app : FStar_ToSMT_Term.op  ->  Prims.bool = (fun _47_8 -> (match (_47_8) with
| (FStar_ToSMT_Term.Var ("ApplyTT")) | (FStar_ToSMT_Term.Var ("ApplyTE")) | (FStar_ToSMT_Term.Var ("ApplyET")) | (FStar_ToSMT_Term.Var ("ApplyEE")) -> begin
true
end
| _47_560 -> begin
false
end))

# 338 "FStar.ToSMT.Encode.fst"
let is_eta : env_t  ->  FStar_ToSMT_Term.fv Prims.list  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term Prims.option = (fun env vars t -> (
# 339 "FStar.ToSMT.Encode.fst"
let rec aux = (fun t xs -> (match ((t.FStar_ToSMT_Term.tm, xs)) with
| (FStar_ToSMT_Term.App (app, f::{FStar_ToSMT_Term.tm = FStar_ToSMT_Term.FreeV (y); FStar_ToSMT_Term.hash = _47_571; FStar_ToSMT_Term.freevars = _47_569}::[]), x::xs) when ((is_app app) && (FStar_ToSMT_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_ToSMT_Term.App (FStar_ToSMT_Term.Var (f), args), _47_589) -> begin
if (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (fv) -> begin
(FStar_ToSMT_Term.fv_eq fv v)
end
| _47_596 -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_47_598, []) -> begin
(
# 350 "FStar.ToSMT.Encode.fst"
let fvs = (FStar_ToSMT_Term.free_variables t)
in if (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (not ((FStar_Util.for_some (FStar_ToSMT_Term.fv_eq fv) vars)))))) then begin
Some (t)
end else begin
None
end)
end
| _47_604 -> begin
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
let encode_const : FStar_Const.sconst  ->  FStar_ToSMT_Term.term = (fun _47_9 -> (match (_47_9) with
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
(let _126_561 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_char c))
in (FStar_ToSMT_Term.boxInt _126_561))
end
| FStar_Const.Const_uint8 (i) -> begin
(let _126_562 = (FStar_ToSMT_Term.mkInteger' (FStar_Util.int_of_uint8 i))
in (FStar_ToSMT_Term.boxInt _126_562))
end
| FStar_Const.Const_int (i) -> begin
(let _126_563 = (FStar_ToSMT_Term.mkInteger i)
in (FStar_ToSMT_Term.boxInt _126_563))
end
| FStar_Const.Const_int32 (i) -> begin
(let _126_567 = (let _126_566 = (let _126_565 = (let _126_564 = (FStar_ToSMT_Term.mkInteger32 i)
in (FStar_ToSMT_Term.boxInt _126_564))
in (_126_565)::[])
in ("FStar.Int32.Int32", _126_566))
in (FStar_ToSMT_Term.mkApp _126_567))
end
| FStar_Const.Const_string (bytes, _47_626) -> begin
(let _126_568 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const _126_568))
end
| c -> begin
(let _126_570 = (let _126_569 = (FStar_Absyn_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s\n" _126_569))
in (FStar_All.failwith _126_570))
end))

# 404 "FStar.ToSMT.Encode.fst"
let as_function_typ : env_t  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax = (fun env t0 -> (
# 405 "FStar.ToSMT.Encode.fst"
let rec aux = (fun norm t -> (
# 406 "FStar.ToSMT.Encode.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (_47_637) -> begin
t
end
| FStar_Absyn_Syntax.Typ_refine (_47_640) -> begin
(let _126_579 = (FStar_Absyn_Util.unrefine t)
in (aux true _126_579))
end
| _47_643 -> begin
if norm then begin
(let _126_580 = (whnf env t)
in (aux false _126_580))
end else begin
(let _126_583 = (let _126_582 = (FStar_Range.string_of_range t0.FStar_Absyn_Syntax.pos)
in (let _126_581 = (FStar_Absyn_Print.typ_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" _126_582 _126_581)))
in (FStar_All.failwith _126_583))
end
end)))
in (aux true t0)))

# 415 "FStar.ToSMT.Encode.fst"
let rec encode_knd_term : FStar_Absyn_Syntax.knd  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun k env -> (match ((let _126_620 = (FStar_Absyn_Util.compress_kind k)
in _126_620.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_type -> begin
(FStar_ToSMT_Term.mk_Kind_type, [])
end
| FStar_Absyn_Syntax.Kind_abbrev (_47_648, k0) -> begin
(
# 420 "FStar.ToSMT.Encode.fst"
let _47_652 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _126_622 = (FStar_Absyn_Print.kind_to_string k)
in (let _126_621 = (FStar_Absyn_Print.kind_to_string k0)
in (FStar_Util.print2 "Encoding kind abbrev %s, expanded to %s\n" _126_622 _126_621)))
end else begin
()
end
in (encode_knd_term k0 env))
end
| FStar_Absyn_Syntax.Kind_uvar (uv, _47_656) -> begin
(let _126_624 = (let _126_623 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Kind_uvar _126_623))
in (_126_624, []))
end
| FStar_Absyn_Syntax.Kind_arrow (bs, kbody) -> begin
(
# 428 "FStar.ToSMT.Encode.fst"
let tsym = (let _126_625 = (varops.fresh "t")
in (_126_625, FStar_ToSMT_Term.Type_sort))
in (
# 429 "FStar.ToSMT.Encode.fst"
let t = (FStar_ToSMT_Term.mkFreeV tsym)
in (
# 430 "FStar.ToSMT.Encode.fst"
let _47_671 = (encode_binders None bs env)
in (match (_47_671) with
| (vars, guards, env', decls, _47_670) -> begin
(
# 431 "FStar.ToSMT.Encode.fst"
let app = (mk_ApplyT t vars)
in (
# 432 "FStar.ToSMT.Encode.fst"
let _47_675 = (encode_knd kbody env' app)
in (match (_47_675) with
| (kbody, decls') -> begin
(
# 434 "FStar.ToSMT.Encode.fst"
let rec aux = (fun app vars guards -> (match ((vars, guards)) with
| ([], []) -> begin
kbody
end
| (x::vars, g::guards) -> begin
(
# 437 "FStar.ToSMT.Encode.fst"
let app = (mk_ApplyT app ((x)::[]))
in (
# 438 "FStar.ToSMT.Encode.fst"
let body = (aux app vars guards)
in (
# 439 "FStar.ToSMT.Encode.fst"
let body = (match (vars) with
| [] -> begin
body
end
| _47_694 -> begin
(let _126_634 = (let _126_633 = (let _126_632 = (FStar_ToSMT_Term.mk_PreKind app)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _126_632))
in (_126_633, body))
in (FStar_ToSMT_Term.mkAnd _126_634))
end)
in (let _126_636 = (let _126_635 = (FStar_ToSMT_Term.mkImp (g, body))
in (((app)::[])::[], (x)::[], _126_635))
in (FStar_ToSMT_Term.mkForall _126_636)))))
end
| _47_697 -> begin
(FStar_All.failwith "Impossible: vars and guards are in 1-1 correspondence")
end))
in (
# 445 "FStar.ToSMT.Encode.fst"
let k_interp = (aux t vars guards)
in (
# 446 "FStar.ToSMT.Encode.fst"
let cvars = (let _126_638 = (FStar_ToSMT_Term.free_variables k_interp)
in (FStar_All.pipe_right _126_638 (FStar_List.filter (fun _47_702 -> (match (_47_702) with
| (x, _47_701) -> begin
(x <> (Prims.fst tsym))
end)))))
in (
# 447 "FStar.ToSMT.Encode.fst"
let tkey = (FStar_ToSMT_Term.mkForall ([], (tsym)::cvars, k_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (k', sorts, _47_708) -> begin
(let _126_641 = (let _126_640 = (let _126_639 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (k', _126_639))
in (FStar_ToSMT_Term.mkApp _126_640))
in (_126_641, []))
end
| None -> begin
(
# 453 "FStar.ToSMT.Encode.fst"
let ksym = (varops.fresh "Kind_arrow")
in (
# 454 "FStar.ToSMT.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 455 "FStar.ToSMT.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _126_642 = (FStar_Tc_Normalize.kind_norm_to_string env.tcenv k)
in Some (_126_642))
end else begin
None
end
in (
# 461 "FStar.ToSMT.Encode.fst"
let kdecl = FStar_ToSMT_Term.DeclFun ((ksym, cvar_sorts, FStar_ToSMT_Term.Kind_sort, caption))
in (
# 463 "FStar.ToSMT.Encode.fst"
let k = (let _126_644 = (let _126_643 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (ksym, _126_643))
in (FStar_ToSMT_Term.mkApp _126_644))
in (
# 464 "FStar.ToSMT.Encode.fst"
let t_has_k = (FStar_ToSMT_Term.mk_HasKind t k)
in (
# 465 "FStar.ToSMT.Encode.fst"
let k_interp = (let _126_653 = (let _126_652 = (let _126_651 = (let _126_650 = (let _126_649 = (let _126_648 = (let _126_647 = (let _126_646 = (let _126_645 = (FStar_ToSMT_Term.mk_PreKind t)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _126_645))
in (_126_646, k_interp))
in (FStar_ToSMT_Term.mkAnd _126_647))
in (t_has_k, _126_648))
in (FStar_ToSMT_Term.mkIff _126_649))
in (((t_has_k)::[])::[], (tsym)::cvars, _126_650))
in (FStar_ToSMT_Term.mkForall _126_651))
in (_126_652, Some ((Prims.strcat ksym " interpretation"))))
in FStar_ToSMT_Term.Assume (_126_653))
in (
# 471 "FStar.ToSMT.Encode.fst"
let k_decls = (FStar_List.append (FStar_List.append decls decls') ((kdecl)::(k_interp)::[]))
in (
# 472 "FStar.ToSMT.Encode.fst"
let _47_720 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (ksym, cvar_sorts, k_decls))
in (k, k_decls))))))))))
end)))))
end)))
end))))
end
| _47_723 -> begin
(let _126_655 = (let _126_654 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.format1 "Unknown kind: %s" _126_654))
in (FStar_All.failwith _126_655))
end))
and encode_knd : FStar_Absyn_Syntax.knd  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decl Prims.list) = (fun k env t -> (
# 480 "FStar.ToSMT.Encode.fst"
let _47_729 = (encode_knd_term k env)
in (match (_47_729) with
| (k, decls) -> begin
(let _126_659 = (FStar_ToSMT_Term.mk_HasKind t k)
in (_126_659, decls))
end)))
and encode_binders : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.binders  ->  env_t  ->  (FStar_ToSMT_Term.fv Prims.list * FStar_ToSMT_Term.term Prims.list * env_t * FStar_ToSMT_Term.decls_t * (FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list) = (fun fuel_opt bs env -> (
# 490 "FStar.ToSMT.Encode.fst"
let _47_733 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _126_663 = (FStar_Absyn_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" _126_663))
end else begin
()
end
in (
# 492 "FStar.ToSMT.Encode.fst"
let _47_783 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun _47_740 b -> (match (_47_740) with
| (vars, guards, env, decls, names) -> begin
(
# 493 "FStar.ToSMT.Encode.fst"
let _47_777 = (match ((Prims.fst b)) with
| FStar_Util.Inl ({FStar_Absyn_Syntax.v = a; FStar_Absyn_Syntax.sort = k; FStar_Absyn_Syntax.p = _47_743}) -> begin
(
# 495 "FStar.ToSMT.Encode.fst"
let a = (unmangle a)
in (
# 496 "FStar.ToSMT.Encode.fst"
let _47_752 = (gen_typ_var env a)
in (match (_47_752) with
| (aasym, aa, env') -> begin
(
# 497 "FStar.ToSMT.Encode.fst"
let _47_753 = if (FStar_Tc_Env.debug env.tcenv (FStar_Options.Other ("Encoding"))) then begin
(let _126_667 = (FStar_Absyn_Print.strBvd a)
in (let _126_666 = (FStar_Absyn_Print.kind_to_string k)
in (FStar_Util.print3 "Encoding type binder %s (%s) at kind %s\n" _126_667 aasym _126_666)))
end else begin
()
end
in (
# 499 "FStar.ToSMT.Encode.fst"
let _47_757 = (encode_knd k env aa)
in (match (_47_757) with
| (guard_a_k, decls') -> begin
((aasym, FStar_ToSMT_Term.Type_sort), guard_a_k, env', decls', FStar_Util.Inl (a))
end)))
end)))
end
| FStar_Util.Inr ({FStar_Absyn_Syntax.v = x; FStar_Absyn_Syntax.sort = t; FStar_Absyn_Syntax.p = _47_759}) -> begin
(
# 507 "FStar.ToSMT.Encode.fst"
let x = (unmangle x)
in (
# 508 "FStar.ToSMT.Encode.fst"
let _47_768 = (gen_term_var env x)
in (match (_47_768) with
| (xxsym, xx, env') -> begin
(
# 509 "FStar.ToSMT.Encode.fst"
let _47_771 = (let _126_668 = (norm_t env t)
in (encode_typ_pred fuel_opt _126_668 env xx))
in (match (_47_771) with
| (guard_x_t, decls') -> begin
((xxsym, FStar_ToSMT_Term.Term_sort), guard_x_t, env', decls', FStar_Util.Inr (x))
end))
end)))
end)
in (match (_47_777) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (FStar_List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])))
in (match (_47_783) with
| (vars, guards, env, decls, names) -> begin
((FStar_List.rev vars), (FStar_List.rev guards), env, decls, (FStar_List.rev names))
end))))
and encode_typ_pred : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun fuel_opt t env e -> (
# 524 "FStar.ToSMT.Encode.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (
# 525 "FStar.ToSMT.Encode.fst"
let _47_791 = (encode_typ_term t env)
in (match (_47_791) with
| (t, decls) -> begin
(let _126_673 = (FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t)
in (_126_673, decls))
end))))
and encode_typ_pred' : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun fuel_opt t env e -> (
# 529 "FStar.ToSMT.Encode.fst"
let t = (FStar_Absyn_Util.compress_typ t)
in (
# 530 "FStar.ToSMT.Encode.fst"
let _47_799 = (encode_typ_term t env)
in (match (_47_799) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(let _126_678 = (FStar_ToSMT_Term.mk_HasTypeZ e t)
in (_126_678, decls))
end
| Some (f) -> begin
(let _126_679 = (FStar_ToSMT_Term.mk_HasTypeFuel f e t)
in (_126_679, decls))
end)
end))))
and encode_typ_term : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun t env -> (
# 537 "FStar.ToSMT.Encode.fst"
let t0 = (FStar_Absyn_Util.compress_typ t)
in (match (t0.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let _126_682 = (lookup_typ_var env a)
in (_126_682, []))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _126_683 = (lookup_free_tvar env fv)
in (_126_683, []))
end
| FStar_Absyn_Syntax.Typ_fun (binders, res) -> begin
if ((env.encode_non_total_function_typ && (FStar_Absyn_Util.is_pure_or_ghost_comp res)) || (FStar_Absyn_Util.is_tot_or_gtot_comp res)) then begin
(
# 550 "FStar.ToSMT.Encode.fst"
let _47_820 = (encode_binders None binders env)
in (match (_47_820) with
| (vars, guards, env', decls, _47_819) -> begin
(
# 551 "FStar.ToSMT.Encode.fst"
let fsym = (let _126_684 = (varops.fresh "f")
in (_126_684, FStar_ToSMT_Term.Term_sort))
in (
# 552 "FStar.ToSMT.Encode.fst"
let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (
# 553 "FStar.ToSMT.Encode.fst"
let app = (mk_ApplyE f vars)
in (
# 554 "FStar.ToSMT.Encode.fst"
let _47_826 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv res)
in (match (_47_826) with
| (pre_opt, res_t) -> begin
(
# 555 "FStar.ToSMT.Encode.fst"
let _47_829 = (encode_typ_pred None res_t env' app)
in (match (_47_829) with
| (res_pred, decls') -> begin
(
# 556 "FStar.ToSMT.Encode.fst"
let _47_838 = (match (pre_opt) with
| None -> begin
(let _126_685 = (FStar_ToSMT_Term.mk_and_l guards)
in (_126_685, decls))
end
| Some (pre) -> begin
(
# 559 "FStar.ToSMT.Encode.fst"
let _47_835 = (encode_formula pre env')
in (match (_47_835) with
| (guard, decls0) -> begin
(let _126_686 = (FStar_ToSMT_Term.mk_and_l ((guard)::guards))
in (_126_686, (FStar_List.append decls decls0)))
end))
end)
in (match (_47_838) with
| (guards, guard_decls) -> begin
(
# 561 "FStar.ToSMT.Encode.fst"
let t_interp = (let _126_688 = (let _126_687 = (FStar_ToSMT_Term.mkImp (guards, res_pred))
in (((app)::[])::[], vars, _126_687))
in (FStar_ToSMT_Term.mkForall _126_688))
in (
# 566 "FStar.ToSMT.Encode.fst"
let cvars = (let _126_690 = (FStar_ToSMT_Term.free_variables t_interp)
in (FStar_All.pipe_right _126_690 (FStar_List.filter (fun _47_843 -> (match (_47_843) with
| (x, _47_842) -> begin
(x <> (Prims.fst fsym))
end)))))
in (
# 567 "FStar.ToSMT.Encode.fst"
let tkey = (FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t', sorts, _47_849) -> begin
(let _126_693 = (let _126_692 = (let _126_691 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t', _126_691))
in (FStar_ToSMT_Term.mkApp _126_692))
in (_126_693, []))
end
| None -> begin
(
# 573 "FStar.ToSMT.Encode.fst"
let tsym = (varops.fresh "Typ_fun")
in (
# 574 "FStar.ToSMT.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 575 "FStar.ToSMT.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _126_694 = (FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0)
in Some (_126_694))
end else begin
None
end
in (
# 580 "FStar.ToSMT.Encode.fst"
let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, caption))
in (
# 582 "FStar.ToSMT.Encode.fst"
let t = (let _126_696 = (let _126_695 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _126_695))
in (FStar_ToSMT_Term.mkApp _126_696))
in (
# 583 "FStar.ToSMT.Encode.fst"
let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (
# 585 "FStar.ToSMT.Encode.fst"
let k_assumption = (let _126_698 = (let _126_697 = (FStar_ToSMT_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (_126_697, Some ((Prims.strcat tsym " kinding"))))
in FStar_ToSMT_Term.Assume (_126_698))
in (
# 587 "FStar.ToSMT.Encode.fst"
let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (
# 588 "FStar.ToSMT.Encode.fst"
let f_has_t_z = (FStar_ToSMT_Term.mk_HasTypeZ f t)
in (
# 589 "FStar.ToSMT.Encode.fst"
let pre_typing = (let _126_705 = (let _126_704 = (let _126_703 = (let _126_702 = (let _126_701 = (let _126_700 = (let _126_699 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _126_699))
in (f_has_t, _126_700))
in (FStar_ToSMT_Term.mkImp _126_701))
in (((f_has_t)::[])::[], (fsym)::cvars, _126_702))
in (mkForall_fuel _126_703))
in (_126_704, Some ("pre-typing for functions")))
in FStar_ToSMT_Term.Assume (_126_705))
in (
# 590 "FStar.ToSMT.Encode.fst"
let t_interp = (let _126_709 = (let _126_708 = (let _126_707 = (let _126_706 = (FStar_ToSMT_Term.mkIff (f_has_t_z, t_interp))
in (((f_has_t_z)::[])::[], (fsym)::cvars, _126_706))
in (FStar_ToSMT_Term.mkForall _126_707))
in (_126_708, Some ((Prims.strcat tsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_126_709))
in (
# 593 "FStar.ToSMT.Encode.fst"
let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (
# 594 "FStar.ToSMT.Encode.fst"
let _47_865 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))))))
end))))
end))
end))
end)))))
end))
end else begin
(
# 598 "FStar.ToSMT.Encode.fst"
let tsym = (varops.fresh "Non_total_Typ_fun")
in (
# 599 "FStar.ToSMT.Encode.fst"
let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, [], FStar_ToSMT_Term.Type_sort, None))
in (
# 600 "FStar.ToSMT.Encode.fst"
let t = (FStar_ToSMT_Term.mkApp (tsym, []))
in (
# 601 "FStar.ToSMT.Encode.fst"
let t_kinding = (let _126_711 = (let _126_710 = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (_126_710, None))
in FStar_ToSMT_Term.Assume (_126_711))
in (
# 602 "FStar.ToSMT.Encode.fst"
let fsym = ("f", FStar_ToSMT_Term.Term_sort)
in (
# 603 "FStar.ToSMT.Encode.fst"
let f = (FStar_ToSMT_Term.mkFreeV fsym)
in (
# 604 "FStar.ToSMT.Encode.fst"
let f_has_t = (FStar_ToSMT_Term.mk_HasType f t)
in (
# 605 "FStar.ToSMT.Encode.fst"
let t_interp = (let _126_718 = (let _126_717 = (let _126_716 = (let _126_715 = (let _126_714 = (let _126_713 = (let _126_712 = (FStar_ToSMT_Term.mk_PreType f)
in (FStar_ToSMT_Term.mk_tester "Typ_fun" _126_712))
in (f_has_t, _126_713))
in (FStar_ToSMT_Term.mkImp _126_714))
in (((f_has_t)::[])::[], (fsym)::[], _126_715))
in (mkForall_fuel _126_716))
in (_126_717, Some ("pre-typing")))
in FStar_ToSMT_Term.Assume (_126_718))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end
| FStar_Absyn_Syntax.Typ_refine (_47_876) -> begin
(
# 612 "FStar.ToSMT.Encode.fst"
let _47_895 = (match ((FStar_Tc_Normalize.normalize_refinement [] env.tcenv t0)) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_refine (x, f); FStar_Absyn_Syntax.tk = _47_885; FStar_Absyn_Syntax.pos = _47_883; FStar_Absyn_Syntax.fvs = _47_881; FStar_Absyn_Syntax.uvs = _47_879} -> begin
(x, f)
end
| _47_892 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_47_895) with
| (x, f) -> begin
(
# 616 "FStar.ToSMT.Encode.fst"
let _47_898 = (encode_typ_term x.FStar_Absyn_Syntax.sort env)
in (match (_47_898) with
| (base_t, decls) -> begin
(
# 617 "FStar.ToSMT.Encode.fst"
let _47_902 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_47_902) with
| (x, xtm, env') -> begin
(
# 618 "FStar.ToSMT.Encode.fst"
let _47_905 = (encode_formula f env')
in (match (_47_905) with
| (refinement, decls') -> begin
(
# 620 "FStar.ToSMT.Encode.fst"
let _47_908 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_47_908) with
| (fsym, fterm) -> begin
(
# 622 "FStar.ToSMT.Encode.fst"
let encoding = (let _126_720 = (let _126_719 = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in (_126_719, refinement))
in (FStar_ToSMT_Term.mkAnd _126_720))
in (
# 624 "FStar.ToSMT.Encode.fst"
let cvars = (let _126_722 = (FStar_ToSMT_Term.free_variables encoding)
in (FStar_All.pipe_right _126_722 (FStar_List.filter (fun _47_913 -> (match (_47_913) with
| (y, _47_912) -> begin
((y <> x) && (y <> fsym))
end)))))
in (
# 625 "FStar.ToSMT.Encode.fst"
let xfv = (x, FStar_ToSMT_Term.Term_sort)
in (
# 626 "FStar.ToSMT.Encode.fst"
let ffv = (fsym, FStar_ToSMT_Term.Fuel_sort)
in (
# 627 "FStar.ToSMT.Encode.fst"
let tkey = (FStar_ToSMT_Term.mkForall ([], (ffv)::(xfv)::cvars, encoding))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _47_920, _47_922) -> begin
(let _126_725 = (let _126_724 = (let _126_723 = (FStar_All.pipe_right cvars (FStar_List.map FStar_ToSMT_Term.mkFreeV))
in (t, _126_723))
in (FStar_ToSMT_Term.mkApp _126_724))
in (_126_725, []))
end
| None -> begin
(
# 634 "FStar.ToSMT.Encode.fst"
let tsym = (varops.fresh "Typ_refine")
in (
# 635 "FStar.ToSMT.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 636 "FStar.ToSMT.Encode.fst"
let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, None))
in (
# 637 "FStar.ToSMT.Encode.fst"
let t = (let _126_727 = (let _126_726 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _126_726))
in (FStar_ToSMT_Term.mkApp _126_727))
in (
# 639 "FStar.ToSMT.Encode.fst"
let x_has_t = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (
# 640 "FStar.ToSMT.Encode.fst"
let t_has_kind = (FStar_ToSMT_Term.mk_HasKind t FStar_ToSMT_Term.mk_Kind_type)
in (
# 642 "FStar.ToSMT.Encode.fst"
let t_kinding = (FStar_ToSMT_Term.mkForall (((t_has_kind)::[])::[], cvars, t_has_kind))
in (
# 643 "FStar.ToSMT.Encode.fst"
let assumption = (let _126_729 = (let _126_728 = (FStar_ToSMT_Term.mkIff (x_has_t, encoding))
in (((x_has_t)::[])::[], (ffv)::(xfv)::cvars, _126_728))
in (FStar_ToSMT_Term.mkForall _126_729))
in (
# 645 "FStar.ToSMT.Encode.fst"
let t_decls = (let _126_736 = (let _126_735 = (let _126_734 = (let _126_733 = (let _126_732 = (let _126_731 = (let _126_730 = (FStar_Absyn_Print.typ_to_string t0)
in Some (_126_730))
in (assumption, _126_731))
in FStar_ToSMT_Term.Assume (_126_732))
in (_126_733)::[])
in (FStar_ToSMT_Term.Assume ((t_kinding, None)))::_126_734)
in (tdecl)::_126_735)
in (FStar_List.append (FStar_List.append decls decls') _126_736))
in (
# 650 "FStar.ToSMT.Encode.fst"
let _47_935 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
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
# 655 "FStar.ToSMT.Encode.fst"
let ttm = (let _126_737 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _126_737))
in (
# 656 "FStar.ToSMT.Encode.fst"
let _47_944 = (encode_knd k env ttm)
in (match (_47_944) with
| (t_has_k, decls) -> begin
(
# 657 "FStar.ToSMT.Encode.fst"
let d = FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| FStar_Absyn_Syntax.Typ_app (head, args) -> begin
(
# 661 "FStar.ToSMT.Encode.fst"
let is_full_app = (fun _47_951 -> (match (()) with
| () -> begin
(
# 662 "FStar.ToSMT.Encode.fst"
let kk = (FStar_Tc_Recheck.recompute_kind head)
in (
# 663 "FStar.ToSMT.Encode.fst"
let _47_956 = (FStar_Absyn_Util.kind_formals kk)
in (match (_47_956) with
| (formals, _47_955) -> begin
((FStar_List.length formals) = (FStar_List.length args))
end)))
end))
in (
# 665 "FStar.ToSMT.Encode.fst"
let head = (FStar_Absyn_Util.compress_typ head)
in (match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(
# 668 "FStar.ToSMT.Encode.fst"
let head = (lookup_typ_var env a)
in (
# 669 "FStar.ToSMT.Encode.fst"
let _47_963 = (encode_args args env)
in (match (_47_963) with
| (args, decls) -> begin
(
# 670 "FStar.ToSMT.Encode.fst"
let t = (mk_ApplyT_args head args)
in (t, decls))
end)))
end
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(
# 674 "FStar.ToSMT.Encode.fst"
let _47_969 = (encode_args args env)
in (match (_47_969) with
| (args, decls) -> begin
if (is_full_app ()) then begin
(
# 676 "FStar.ToSMT.Encode.fst"
let head = (lookup_free_tvar_name env fv)
in (
# 677 "FStar.ToSMT.Encode.fst"
let t = (let _126_742 = (let _126_741 = (FStar_List.map (fun _47_10 -> (match (_47_10) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (head, _126_741))
in (FStar_ToSMT_Term.mkApp _126_742))
in (t, decls)))
end else begin
(
# 679 "FStar.ToSMT.Encode.fst"
let head = (lookup_free_tvar env fv)
in (
# 680 "FStar.ToSMT.Encode.fst"
let t = (mk_ApplyT_args head args)
in (t, decls)))
end
end))
end
| FStar_Absyn_Syntax.Typ_uvar (uv, k) -> begin
(
# 684 "FStar.ToSMT.Encode.fst"
let ttm = (let _126_743 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Typ_uvar _126_743))
in (
# 685 "FStar.ToSMT.Encode.fst"
let _47_985 = (encode_knd k env ttm)
in (match (_47_985) with
| (t_has_k, decls) -> begin
(
# 686 "FStar.ToSMT.Encode.fst"
let d = FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| _47_988 -> begin
(
# 690 "FStar.ToSMT.Encode.fst"
let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| FStar_Absyn_Syntax.Typ_lam (bs, body) -> begin
(
# 698 "FStar.ToSMT.Encode.fst"
let _47_1000 = (encode_binders None bs env)
in (match (_47_1000) with
| (vars, guards, env, decls, _47_999) -> begin
(
# 699 "FStar.ToSMT.Encode.fst"
let _47_1003 = (encode_typ_term body env)
in (match (_47_1003) with
| (body, decls') -> begin
(
# 701 "FStar.ToSMT.Encode.fst"
let key_body = (let _126_747 = (let _126_746 = (let _126_745 = (let _126_744 = (FStar_ToSMT_Term.mk_and_l guards)
in (_126_744, body))
in (FStar_ToSMT_Term.mkImp _126_745))
in ([], vars, _126_746))
in (FStar_ToSMT_Term.mkForall _126_747))
in (
# 702 "FStar.ToSMT.Encode.fst"
let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (
# 703 "FStar.ToSMT.Encode.fst"
let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _47_1009, _47_1011) -> begin
(let _126_750 = (let _126_749 = (let _126_748 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _126_748))
in (FStar_ToSMT_Term.mkApp _126_749))
in (_126_750, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (head) -> begin
(head, [])
end
| None -> begin
(
# 715 "FStar.ToSMT.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 716 "FStar.ToSMT.Encode.fst"
let tsym = (varops.fresh "Typ_lam")
in (
# 717 "FStar.ToSMT.Encode.fst"
let tdecl = FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, FStar_ToSMT_Term.Type_sort, None))
in (
# 718 "FStar.ToSMT.Encode.fst"
let t = (let _126_752 = (let _126_751 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (tsym, _126_751))
in (FStar_ToSMT_Term.mkApp _126_752))
in (
# 719 "FStar.ToSMT.Encode.fst"
let app = (mk_ApplyT t vars)
in (
# 721 "FStar.ToSMT.Encode.fst"
let interp = (let _126_759 = (let _126_758 = (let _126_757 = (let _126_756 = (let _126_755 = (let _126_754 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _126_753 = (FStar_ToSMT_Term.mkEq (app, body))
in (_126_754, _126_753)))
in (FStar_ToSMT_Term.mkImp _126_755))
in (((app)::[])::[], (FStar_List.append vars cvars), _126_756))
in (FStar_ToSMT_Term.mkForall _126_757))
in (_126_758, Some ("Typ_lam interpretation")))
in FStar_ToSMT_Term.Assume (_126_759))
in (
# 724 "FStar.ToSMT.Encode.fst"
let kinding = (
# 725 "FStar.ToSMT.Encode.fst"
let _47_1026 = (let _126_760 = (FStar_Tc_Recheck.recompute_kind t0)
in (encode_knd _126_760 env t))
in (match (_47_1026) with
| (ktm, decls'') -> begin
(let _126_764 = (let _126_763 = (let _126_762 = (let _126_761 = (FStar_ToSMT_Term.mkForall (((t)::[])::[], cvars, ktm))
in (_126_761, Some ("Typ_lam kinding")))
in FStar_ToSMT_Term.Assume (_126_762))
in (_126_763)::[])
in (FStar_List.append decls'' _126_764))
end))
in (
# 728 "FStar.ToSMT.Encode.fst"
let t_decls = (FStar_List.append (FStar_List.append decls decls') ((tdecl)::(interp)::kinding))
in (
# 730 "FStar.ToSMT.Encode.fst"
let _47_1029 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))
end)
end))))
end))
end))
end
| FStar_Absyn_Syntax.Typ_ascribed (t, _47_1033) -> begin
(encode_typ_term t env)
end
| FStar_Absyn_Syntax.Typ_meta (_47_1037) -> begin
(let _126_765 = (FStar_Absyn_Util.unmeta_typ t0)
in (encode_typ_term _126_765 env))
end
| (FStar_Absyn_Syntax.Typ_delayed (_)) | (FStar_Absyn_Syntax.Typ_unknown) -> begin
(let _126_770 = (let _126_769 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Absyn_Syntax.pos)
in (let _126_768 = (FStar_Absyn_Print.tag_of_typ t0)
in (let _126_767 = (FStar_Absyn_Print.typ_to_string t0)
in (let _126_766 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" _126_769 _126_768 _126_767 _126_766)))))
in (FStar_All.failwith _126_770))
end)))
and encode_exp : FStar_Absyn_Syntax.exp  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun e env -> (
# 746 "FStar.ToSMT.Encode.fst"
let e = (FStar_Absyn_Visit.compress_exp_uvars e)
in (
# 747 "FStar.ToSMT.Encode.fst"
let e0 = e
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_delayed (_47_1048) -> begin
(let _126_773 = (FStar_Absyn_Util.compress_exp e)
in (encode_exp _126_773 env))
end
| FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(
# 753 "FStar.ToSMT.Encode.fst"
let t = (lookup_term_var env x)
in (t, []))
end
| FStar_Absyn_Syntax.Exp_fvar (v, _47_1055) -> begin
(let _126_774 = (lookup_free_var env v)
in (_126_774, []))
end
| FStar_Absyn_Syntax.Exp_constant (c) -> begin
(let _126_775 = (encode_const c)
in (_126_775, []))
end
| FStar_Absyn_Syntax.Exp_ascribed (e, t, _47_1063) -> begin
(
# 763 "FStar.ToSMT.Encode.fst"
let _47_1066 = (FStar_ST.op_Colon_Equals e.FStar_Absyn_Syntax.tk (Some (t)))
in (encode_exp e env))
end
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared (e, _47_1070)) -> begin
(encode_exp e env)
end
| FStar_Absyn_Syntax.Exp_uvar (uv, _47_1076) -> begin
(
# 771 "FStar.ToSMT.Encode.fst"
let e = (let _126_776 = (FStar_Unionfind.uvar_id uv)
in (FStar_ToSMT_Term.mk_Exp_uvar _126_776))
in (e, []))
end
| FStar_Absyn_Syntax.Exp_abs (bs, body) -> begin
(
# 775 "FStar.ToSMT.Encode.fst"
let fallback = (fun _47_1085 -> (match (()) with
| () -> begin
(
# 776 "FStar.ToSMT.Encode.fst"
let f = (varops.fresh "Exp_abs")
in (
# 777 "FStar.ToSMT.Encode.fst"
let decl = FStar_ToSMT_Term.DeclFun ((f, [], FStar_ToSMT_Term.Term_sort, None))
in (let _126_779 = (FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
in (_126_779, (decl)::[]))))
end))
in (match ((FStar_ST.read e.FStar_Absyn_Syntax.tk)) with
| None -> begin
(
# 782 "FStar.ToSMT.Encode.fst"
let _47_1089 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
if (let _126_780 = (FStar_Absyn_Util.is_pure_or_ghost_function tfun)
in (FStar_All.pipe_left Prims.op_Negation _126_780)) then begin
(fallback ())
end else begin
(
# 787 "FStar.ToSMT.Encode.fst"
let tfun = (as_function_typ env tfun)
in (match (tfun.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (bs', c) -> begin
(
# 790 "FStar.ToSMT.Encode.fst"
let nformals = (FStar_List.length bs')
in if ((nformals < (FStar_List.length bs)) && (FStar_Absyn_Util.is_total_comp c)) then begin
(
# 799 "FStar.ToSMT.Encode.fst"
let _47_1101 = (FStar_Util.first_N nformals bs)
in (match (_47_1101) with
| (bs0, rest) -> begin
(
# 800 "FStar.ToSMT.Encode.fst"
let res_t = (match ((FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s (FStar_Absyn_Util.comp_result c))
end
| _47_1105 -> begin
(FStar_All.failwith "Impossible")
end)
in (
# 803 "FStar.ToSMT.Encode.fst"
let e = (let _126_782 = (let _126_781 = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.FStar_Absyn_Syntax.pos)
in (bs0, _126_781))
in (FStar_Absyn_Syntax.mk_Exp_abs _126_782 (Some (tfun)) e0.FStar_Absyn_Syntax.pos))
in (encode_exp e env)))
end))
end else begin
(
# 808 "FStar.ToSMT.Encode.fst"
let _47_1114 = (encode_binders None bs env)
in (match (_47_1114) with
| (vars, guards, envbody, decls, _47_1113) -> begin
(
# 809 "FStar.ToSMT.Encode.fst"
let _47_1117 = (encode_exp body envbody)
in (match (_47_1117) with
| (body, decls') -> begin
(
# 811 "FStar.ToSMT.Encode.fst"
let key_body = (let _126_786 = (let _126_785 = (let _126_784 = (let _126_783 = (FStar_ToSMT_Term.mk_and_l guards)
in (_126_783, body))
in (FStar_ToSMT_Term.mkImp _126_784))
in ([], vars, _126_785))
in (FStar_ToSMT_Term.mkForall _126_786))
in (
# 812 "FStar.ToSMT.Encode.fst"
let cvars = (FStar_ToSMT_Term.free_variables key_body)
in (
# 813 "FStar.ToSMT.Encode.fst"
let tkey = (FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((FStar_Util.smap_try_find env.cache tkey.FStar_ToSMT_Term.hash)) with
| Some (t, _47_1123, _47_1125) -> begin
(let _126_789 = (let _126_788 = (let _126_787 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (t, _126_787))
in (FStar_ToSMT_Term.mkApp _126_788))
in (_126_789, []))
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
(t, [])
end
| None -> begin
(
# 824 "FStar.ToSMT.Encode.fst"
let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (
# 825 "FStar.ToSMT.Encode.fst"
let fsym = (varops.fresh "Exp_abs")
in (
# 826 "FStar.ToSMT.Encode.fst"
let fdecl = FStar_ToSMT_Term.DeclFun ((fsym, cvar_sorts, FStar_ToSMT_Term.Term_sort, None))
in (
# 827 "FStar.ToSMT.Encode.fst"
let f = (let _126_791 = (let _126_790 = (FStar_List.map FStar_ToSMT_Term.mkFreeV cvars)
in (fsym, _126_790))
in (FStar_ToSMT_Term.mkApp _126_791))
in (
# 828 "FStar.ToSMT.Encode.fst"
let app = (mk_ApplyE f vars)
in (
# 830 "FStar.ToSMT.Encode.fst"
let _47_1139 = (encode_typ_pred None tfun env f)
in (match (_47_1139) with
| (f_has_t, decls'') -> begin
(
# 831 "FStar.ToSMT.Encode.fst"
let typing_f = (let _126_793 = (let _126_792 = (FStar_ToSMT_Term.mkForall (((f)::[])::[], cvars, f_has_t))
in (_126_792, Some ((Prims.strcat fsym " typing"))))
in FStar_ToSMT_Term.Assume (_126_793))
in (
# 834 "FStar.ToSMT.Encode.fst"
let interp_f = (let _126_800 = (let _126_799 = (let _126_798 = (let _126_797 = (let _126_796 = (let _126_795 = (FStar_ToSMT_Term.mk_IsTyped app)
in (let _126_794 = (FStar_ToSMT_Term.mkEq (app, body))
in (_126_795, _126_794)))
in (FStar_ToSMT_Term.mkImp _126_796))
in (((app)::[])::[], (FStar_List.append vars cvars), _126_797))
in (FStar_ToSMT_Term.mkForall _126_798))
in (_126_799, Some ((Prims.strcat fsym " interpretation"))))
in FStar_ToSMT_Term.Assume (_126_800))
in (
# 837 "FStar.ToSMT.Encode.fst"
let f_decls = (FStar_List.append (FStar_List.append (FStar_List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (
# 839 "FStar.ToSMT.Encode.fst"
let _47_1143 = (FStar_Util.smap_add env.cache tkey.FStar_ToSMT_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end)))))))
end)
end))))
end))
end))
end)
end
| _47_1146 -> begin
(FStar_All.failwith "Impossible")
end))
end
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (l, _47_1157); FStar_Absyn_Syntax.tk = _47_1154; FStar_Absyn_Syntax.pos = _47_1152; FStar_Absyn_Syntax.fvs = _47_1150; FStar_Absyn_Syntax.uvs = _47_1148}, (FStar_Util.Inl (_47_1172), _47_1175)::(FStar_Util.Inr (v1), _47_1169)::(FStar_Util.Inr (v2), _47_1164)::[]) when (FStar_Ident.lid_equals l.FStar_Absyn_Syntax.v FStar_Absyn_Const.lexcons_lid) -> begin
(
# 849 "FStar.ToSMT.Encode.fst"
let _47_1182 = (encode_exp v1 env)
in (match (_47_1182) with
| (v1, decls1) -> begin
(
# 850 "FStar.ToSMT.Encode.fst"
let _47_1185 = (encode_exp v2 env)
in (match (_47_1185) with
| (v2, decls2) -> begin
(let _126_801 = (FStar_ToSMT_Term.mk_LexCons v1 v2)
in (_126_801, (FStar_List.append decls1 decls2)))
end))
end))
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (_47_1195); FStar_Absyn_Syntax.tk = _47_1193; FStar_Absyn_Syntax.pos = _47_1191; FStar_Absyn_Syntax.fvs = _47_1189; FStar_Absyn_Syntax.uvs = _47_1187}, _47_1199) -> begin
(let _126_802 = (whnf_e env e)
in (encode_exp _126_802 env))
end
| FStar_Absyn_Syntax.Exp_app (head, args_e) -> begin
(
# 857 "FStar.ToSMT.Encode.fst"
let _47_1208 = (encode_args args_e env)
in (match (_47_1208) with
| (args, decls) -> begin
(
# 859 "FStar.ToSMT.Encode.fst"
let encode_partial_app = (fun ht_opt -> (
# 860 "FStar.ToSMT.Encode.fst"
let _47_1213 = (encode_exp head env)
in (match (_47_1213) with
| (head, decls') -> begin
(
# 861 "FStar.ToSMT.Encode.fst"
let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (FStar_List.append decls decls'))
end
| Some (formals, c) -> begin
(
# 865 "FStar.ToSMT.Encode.fst"
let _47_1222 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (_47_1222) with
| (formals, rest) -> begin
(
# 866 "FStar.ToSMT.Encode.fst"
let subst = (FStar_Absyn_Util.formals_for_actuals formals args_e)
in (
# 867 "FStar.ToSMT.Encode.fst"
let ty = (let _126_805 = (FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (FStar_Absyn_Syntax.ktype)) e0.FStar_Absyn_Syntax.pos)
in (FStar_All.pipe_right _126_805 (FStar_Absyn_Util.subst_typ subst)))
in (
# 868 "FStar.ToSMT.Encode.fst"
let _47_1227 = (encode_typ_pred None ty env app_tm)
in (match (_47_1227) with
| (has_type, decls'') -> begin
(
# 869 "FStar.ToSMT.Encode.fst"
let cvars = (FStar_ToSMT_Term.free_variables has_type)
in (
# 870 "FStar.ToSMT.Encode.fst"
let e_typing = (let _126_807 = (let _126_806 = (FStar_ToSMT_Term.mkForall (((has_type)::[])::[], cvars, has_type))
in (_126_806, None))
in FStar_ToSMT_Term.Assume (_126_807))
in (app_tm, (FStar_List.append (FStar_List.append (FStar_List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (
# 874 "FStar.ToSMT.Encode.fst"
let encode_full_app = (fun fv -> (
# 875 "FStar.ToSMT.Encode.fst"
let _47_1234 = (lookup_free_var_sym env fv)
in (match (_47_1234) with
| (fname, fuel_args) -> begin
(
# 876 "FStar.ToSMT.Encode.fst"
let tm = (let _126_813 = (let _126_812 = (let _126_811 = (FStar_List.map (fun _47_11 -> (match (_47_11) with
| (FStar_Util.Inl (t)) | (FStar_Util.Inr (t)) -> begin
t
end)) args)
in (FStar_List.append fuel_args _126_811))
in (fname, _126_812))
in (FStar_ToSMT_Term.mkApp' _126_813))
in (tm, decls))
end)))
in (
# 879 "FStar.ToSMT.Encode.fst"
let head = (FStar_Absyn_Util.compress_exp head)
in (
# 881 "FStar.ToSMT.Encode.fst"
let _47_1241 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("186"))) then begin
(let _126_815 = (FStar_Absyn_Print.exp_to_string head)
in (let _126_814 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.print2 "Recomputing type for %s\nFull term is %s\n" _126_815 _126_814)))
end else begin
()
end
in (
# 884 "FStar.ToSMT.Encode.fst"
let head_type = (let _126_818 = (let _126_817 = (let _126_816 = (FStar_Tc_Recheck.recompute_typ head)
in (FStar_Absyn_Util.unrefine _126_816))
in (whnf env _126_817))
in (FStar_All.pipe_left FStar_Absyn_Util.unrefine _126_818))
in (
# 886 "FStar.ToSMT.Encode.fst"
let _47_1244 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _126_821 = (FStar_Absyn_Print.exp_to_string head)
in (let _126_820 = (FStar_Absyn_Print.tag_of_exp head)
in (let _126_819 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.print3 "Recomputed type of head %s (%s) to be %s\n" _126_821 _126_820 _126_819))))
end else begin
()
end
in (match ((FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(let _126_825 = (let _126_824 = (FStar_Range.string_of_range e0.FStar_Absyn_Syntax.pos)
in (let _126_823 = (FStar_Absyn_Print.exp_to_string e0)
in (let _126_822 = (FStar_Absyn_Print.typ_to_string head_type)
in (FStar_Util.format3 "(%s) term is %s; head type is %s\n" _126_824 _126_823 _126_822))))
in (FStar_All.failwith _126_825))
end
| Some (formals, c) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (fv, _47_1253) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv)
end
| _47_1257 -> begin
if ((FStar_List.length formals) > (FStar_List.length args)) then begin
(encode_partial_app (Some ((formals, c))))
end else begin
(encode_partial_app None)
end
end)
end)))))))
end))
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (_47_1266); FStar_Absyn_Syntax.lbtyp = _47_1264; FStar_Absyn_Syntax.lbeff = _47_1262; FStar_Absyn_Syntax.lbdef = _47_1260}::[]), _47_1272) -> begin
(FStar_All.failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Absyn_Syntax.Exp_let ((false, {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (x); FStar_Absyn_Syntax.lbtyp = t1; FStar_Absyn_Syntax.lbeff = _47_1278; FStar_Absyn_Syntax.lbdef = e1}::[]), e2) -> begin
(
# 906 "FStar.ToSMT.Encode.fst"
let _47_1290 = (encode_exp e1 env)
in (match (_47_1290) with
| (ee1, decls1) -> begin
(
# 907 "FStar.ToSMT.Encode.fst"
let env' = (push_term_var env x ee1)
in (
# 908 "FStar.ToSMT.Encode.fst"
let _47_1294 = (encode_exp e2 env')
in (match (_47_1294) with
| (ee2, decls2) -> begin
(ee2, (FStar_List.append decls1 decls2))
end)))
end))
end
| FStar_Absyn_Syntax.Exp_let (_47_1296) -> begin
(
# 912 "FStar.ToSMT.Encode.fst"
let _47_1298 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (
# 913 "FStar.ToSMT.Encode.fst"
let e = (varops.fresh "let-rec")
in (
# 914 "FStar.ToSMT.Encode.fst"
let decl_e = FStar_ToSMT_Term.DeclFun ((e, [], FStar_ToSMT_Term.Term_sort, None))
in (let _126_826 = (FStar_ToSMT_Term.mkFreeV (e, FStar_ToSMT_Term.Term_sort))
in (_126_826, (decl_e)::[])))))
end
| FStar_Absyn_Syntax.Exp_match (e, pats) -> begin
(
# 918 "FStar.ToSMT.Encode.fst"
let _47_1308 = (encode_exp e env)
in (match (_47_1308) with
| (scr, decls) -> begin
(
# 921 "FStar.ToSMT.Encode.fst"
let _47_1348 = (FStar_List.fold_right (fun _47_1312 _47_1315 -> (match ((_47_1312, _47_1315)) with
| ((p, w, br), (else_case, decls)) -> begin
(
# 922 "FStar.ToSMT.Encode.fst"
let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun _47_1319 _47_1322 -> (match ((_47_1319, _47_1322)) with
| ((env0, pattern), (else_case, decls)) -> begin
(
# 924 "FStar.ToSMT.Encode.fst"
let guard = (pattern.guard scr)
in (
# 925 "FStar.ToSMT.Encode.fst"
let projections = (pattern.projections scr)
in (
# 926 "FStar.ToSMT.Encode.fst"
let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env _47_1328 -> (match (_47_1328) with
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
# 929 "FStar.ToSMT.Encode.fst"
let _47_1342 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(
# 932 "FStar.ToSMT.Encode.fst"
let _47_1339 = (encode_exp w env)
in (match (_47_1339) with
| (w, decls2) -> begin
(let _126_837 = (let _126_836 = (let _126_835 = (let _126_834 = (let _126_833 = (FStar_ToSMT_Term.boxBool FStar_ToSMT_Term.mkTrue)
in (w, _126_833))
in (FStar_ToSMT_Term.mkEq _126_834))
in (guard, _126_835))
in (FStar_ToSMT_Term.mkAnd _126_836))
in (_126_837, decls2))
end))
end)
in (match (_47_1342) with
| (guard, decls2) -> begin
(
# 934 "FStar.ToSMT.Encode.fst"
let _47_1345 = (encode_exp br env)
in (match (_47_1345) with
| (br, decls3) -> begin
(let _126_838 = (FStar_ToSMT_Term.mkITE (guard, br, else_case))
in (_126_838, (FStar_List.append (FStar_List.append decls decls2) decls3)))
end))
end)))))
end)) patterns (else_case, decls)))
end)) pats (FStar_ToSMT_Term.mk_Term_unit, decls))
in (match (_47_1348) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end))
end
| FStar_Absyn_Syntax.Exp_meta (_47_1350) -> begin
(let _126_841 = (let _126_840 = (FStar_Range.string_of_range e.FStar_Absyn_Syntax.pos)
in (let _126_839 = (FStar_Absyn_Print.exp_to_string e)
in (FStar_Util.format2 "(%s): Impossible: encode_exp got %s" _126_840 _126_839)))
in (FStar_All.failwith _126_841))
end))))
and encode_pat : env_t  ->  FStar_Absyn_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| _47_1357 -> begin
(let _126_844 = (encode_one_pat env pat)
in (_126_844)::[])
end))
and encode_one_pat : env_t  ->  FStar_Absyn_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> (
# 949 "FStar.ToSMT.Encode.fst"
let _47_1360 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _126_847 = (FStar_Absyn_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" _126_847))
end else begin
()
end
in (
# 950 "FStar.ToSMT.Encode.fst"
let _47_1364 = (FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_47_1364) with
| (vars, pat_exp_or_typ) -> begin
(
# 952 "FStar.ToSMT.Encode.fst"
let _47_1385 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun _47_1367 v -> (match (_47_1367) with
| (env, vars) -> begin
(match (v) with
| FStar_Util.Inl (a) -> begin
(
# 954 "FStar.ToSMT.Encode.fst"
let _47_1375 = (gen_typ_var env a.FStar_Absyn_Syntax.v)
in (match (_47_1375) with
| (aa, _47_1373, env) -> begin
(env, ((v, (aa, FStar_ToSMT_Term.Type_sort)))::vars)
end))
end
| FStar_Util.Inr (x) -> begin
(
# 957 "FStar.ToSMT.Encode.fst"
let _47_1382 = (gen_term_var env x.FStar_Absyn_Syntax.v)
in (match (_47_1382) with
| (xx, _47_1380, env) -> begin
(env, ((v, (xx, FStar_ToSMT_Term.Term_sort)))::vars)
end))
end)
end)) (env, [])))
in (match (_47_1385) with
| (env, vars) -> begin
(
# 960 "FStar.ToSMT.Encode.fst"
let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_47_1390) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_twild (_)) | (FStar_Absyn_Syntax.Pat_dot_term (_)) | (FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
FStar_ToSMT_Term.mkTrue
end
| FStar_Absyn_Syntax.Pat_constant (c) -> begin
(let _126_855 = (let _126_854 = (encode_const c)
in (scrutinee, _126_854))
in (FStar_ToSMT_Term.mkEq _126_855))
end
| FStar_Absyn_Syntax.Pat_cons (f, _47_1414, args) -> begin
(
# 971 "FStar.ToSMT.Encode.fst"
let is_f = (mk_data_tester env f.FStar_Absyn_Syntax.v scrutinee)
in (
# 972 "FStar.ToSMT.Encode.fst"
let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i _47_1423 -> (match (_47_1423) with
| (arg, _47_1422) -> begin
(
# 973 "FStar.ToSMT.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _126_858 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_guard arg _126_858)))
end))))
in (FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (
# 977 "FStar.ToSMT.Encode.fst"
let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_disj (_47_1430) -> begin
(FStar_All.failwith "Impossible")
end
| (FStar_Absyn_Syntax.Pat_dot_term (x, _)) | (FStar_Absyn_Syntax.Pat_var (x)) | (FStar_Absyn_Syntax.Pat_wild (x)) -> begin
((FStar_Util.Inr (x), scrutinee))::[]
end
| (FStar_Absyn_Syntax.Pat_dot_typ (a, _)) | (FStar_Absyn_Syntax.Pat_tvar (a)) | (FStar_Absyn_Syntax.Pat_twild (a)) -> begin
((FStar_Util.Inl (a), scrutinee))::[]
end
| FStar_Absyn_Syntax.Pat_constant (_47_1447) -> begin
[]
end
| FStar_Absyn_Syntax.Pat_cons (f, _47_1451, args) -> begin
(let _126_866 = (FStar_All.pipe_right args (FStar_List.mapi (fun i _47_1459 -> (match (_47_1459) with
| (arg, _47_1458) -> begin
(
# 993 "FStar.ToSMT.Encode.fst"
let proj = (primitive_projector_by_pos env.tcenv f.FStar_Absyn_Syntax.v i)
in (let _126_865 = (FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[]))
in (mk_projections arg _126_865)))
end))))
in (FStar_All.pipe_right _126_866 FStar_List.flatten))
end))
in (
# 997 "FStar.ToSMT.Encode.fst"
let pat_term = (fun _47_1462 -> (match (()) with
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
# 1001 "FStar.ToSMT.Encode.fst"
let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args : FStar_Absyn_Syntax.args  ->  env_t  ->  ((FStar_ToSMT_Term.term, FStar_ToSMT_Term.term) FStar_Util.either Prims.list * FStar_ToSMT_Term.decls_t) = (fun l env -> (
# 1011 "FStar.ToSMT.Encode.fst"
let _47_1492 = (FStar_All.pipe_right l (FStar_List.fold_left (fun _47_1472 x -> (match (_47_1472) with
| (tms, decls) -> begin
(match (x) with
| (FStar_Util.Inl (t), _47_1477) -> begin
(
# 1012 "FStar.ToSMT.Encode.fst"
let _47_1481 = (encode_typ_term t env)
in (match (_47_1481) with
| (t, decls') -> begin
((FStar_Util.Inl (t))::tms, (FStar_List.append decls decls'))
end))
end
| (FStar_Util.Inr (e), _47_1485) -> begin
(
# 1013 "FStar.ToSMT.Encode.fst"
let _47_1489 = (encode_exp e env)
in (match (_47_1489) with
| (t, decls') -> begin
((FStar_Util.Inr (t))::tms, (FStar_List.append decls decls'))
end))
end)
end)) ([], [])))
in (match (_47_1492) with
| (l, decls) -> begin
((FStar_List.rev l), decls)
end)))
and encode_formula : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun phi env -> (
# 1017 "FStar.ToSMT.Encode.fst"
let _47_1498 = (encode_formula_with_labels phi env)
in (match (_47_1498) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _47_1501 -> begin
(FStar_All.failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula : FStar_ToSMT_Term.term Prims.option  ->  FStar_Absyn_Syntax.exp Prims.option  ->  FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * FStar_ToSMT_Term.decls_t) = (fun induction_on new_pats t env -> (
# 1024 "FStar.ToSMT.Encode.fst"
let rec list_elements = (fun e -> (match ((let _126_881 = (FStar_Absyn_Util.unmeta_exp e)
in _126_881.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _47_1518); FStar_Absyn_Syntax.tk = _47_1515; FStar_Absyn_Syntax.pos = _47_1513; FStar_Absyn_Syntax.fvs = _47_1511; FStar_Absyn_Syntax.uvs = _47_1509}, _47_1523) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.nil_lid) -> begin
[]
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _47_1536); FStar_Absyn_Syntax.tk = _47_1533; FStar_Absyn_Syntax.pos = _47_1531; FStar_Absyn_Syntax.fvs = _47_1529; FStar_Absyn_Syntax.uvs = _47_1527}, _47_1551::(FStar_Util.Inr (hd), _47_1548)::(FStar_Util.Inr (tl), _47_1543)::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.cons_lid) -> begin
(let _126_882 = (list_elements tl)
in (hd)::_126_882)
end
| _47_1556 -> begin
(
# 1028 "FStar.ToSMT.Encode.fst"
let _47_1557 = (FStar_Tc_Errors.warn e.FStar_Absyn_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern")
in [])
end))
in (
# 1030 "FStar.ToSMT.Encode.fst"
let v_or_t_pat = (fun p -> (match ((let _126_885 = (FStar_Absyn_Util.unmeta_exp p)
in _126_885.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _47_1571); FStar_Absyn_Syntax.tk = _47_1568; FStar_Absyn_Syntax.pos = _47_1566; FStar_Absyn_Syntax.fvs = _47_1564; FStar_Absyn_Syntax.uvs = _47_1562}, (FStar_Util.Inl (_47_1581), _47_1584)::(FStar_Util.Inr (e), _47_1578)::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpat_lid) -> begin
(FStar_Absyn_Syntax.varg e)
end
| FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _47_1599); FStar_Absyn_Syntax.tk = _47_1596; FStar_Absyn_Syntax.pos = _47_1594; FStar_Absyn_Syntax.fvs = _47_1592; FStar_Absyn_Syntax.uvs = _47_1590}, (FStar_Util.Inl (t), _47_1606)::[]) when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatT_lid) -> begin
(FStar_Absyn_Syntax.targ t)
end
| _47_1612 -> begin
(FStar_All.failwith "Unexpected pattern term")
end))
in (
# 1035 "FStar.ToSMT.Encode.fst"
let lemma_pats = (fun p -> (
# 1036 "FStar.ToSMT.Encode.fst"
let elts = (list_elements p)
in (match (elts) with
| {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _47_1634); FStar_Absyn_Syntax.tk = _47_1631; FStar_Absyn_Syntax.pos = _47_1629; FStar_Absyn_Syntax.fvs = _47_1627; FStar_Absyn_Syntax.uvs = _47_1625}, (FStar_Util.Inr (e), _47_1641)::[]); FStar_Absyn_Syntax.tk = _47_1623; FStar_Absyn_Syntax.pos = _47_1621; FStar_Absyn_Syntax.fvs = _47_1619; FStar_Absyn_Syntax.uvs = _47_1617}::[] when (FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.smtpatOr_lid) -> begin
(let _126_890 = (list_elements e)
in (FStar_All.pipe_right _126_890 (FStar_List.map (fun branch -> (let _126_889 = (list_elements branch)
in (FStar_All.pipe_right _126_889 (FStar_List.map v_or_t_pat)))))))
end
| _47_1650 -> begin
(let _126_891 = (FStar_All.pipe_right elts (FStar_List.map v_or_t_pat))
in (_126_891)::[])
end)))
in (
# 1047 "FStar.ToSMT.Encode.fst"
let _47_1693 = (match ((let _126_892 = (FStar_Absyn_Util.compress_typ t)
in _126_892.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_fun (binders, {FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Comp (ct); FStar_Absyn_Syntax.tk = _47_1659; FStar_Absyn_Syntax.pos = _47_1657; FStar_Absyn_Syntax.fvs = _47_1655; FStar_Absyn_Syntax.uvs = _47_1653}) -> begin
(match (ct.FStar_Absyn_Syntax.effect_args) with
| (FStar_Util.Inl (pre), _47_1678)::(FStar_Util.Inl (post), _47_1673)::(FStar_Util.Inr (pats), _47_1668)::[] -> begin
(
# 1051 "FStar.ToSMT.Encode.fst"
let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (let _126_893 = (lemma_pats pats')
in (binders, pre, post, _126_893)))
end
| _47_1686 -> begin
(FStar_All.failwith "impos")
end)
end
| _47_1688 -> begin
(FStar_All.failwith "Impos")
end)
in (match (_47_1693) with
| (binders, pre, post, patterns) -> begin
(
# 1059 "FStar.ToSMT.Encode.fst"
let _47_1700 = (encode_binders None binders env)
in (match (_47_1700) with
| (vars, guards, env, decls, _47_1699) -> begin
(
# 1062 "FStar.ToSMT.Encode.fst"
let _47_1720 = (let _126_897 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (
# 1063 "FStar.ToSMT.Encode.fst"
let _47_1717 = (let _126_896 = (FStar_All.pipe_right branch (FStar_List.map (fun _47_12 -> (match (_47_12) with
| (FStar_Util.Inl (t), _47_1706) -> begin
(encode_formula t env)
end
| (FStar_Util.Inr (e), _47_1711) -> begin
(encode_exp e (
# 1065 "FStar.ToSMT.Encode.fst"
let _47_1713 = env
in {bindings = _47_1713.bindings; depth = _47_1713.depth; tcenv = _47_1713.tcenv; warn = _47_1713.warn; cache = _47_1713.cache; nolabels = _47_1713.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _47_1713.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _126_896 FStar_List.unzip))
in (match (_47_1717) with
| (pats, decls) -> begin
(pats, decls)
end)))))
in (FStar_All.pipe_right _126_897 FStar_List.unzip))
in (match (_47_1720) with
| (pats, decls') -> begin
(
# 1068 "FStar.ToSMT.Encode.fst"
let decls' = (FStar_List.flatten decls')
in (
# 1070 "FStar.ToSMT.Encode.fst"
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
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _126_900 = (let _126_899 = (FStar_ToSMT_Term.mkFreeV l)
in (FStar_ToSMT_Term.mk_Precedes _126_899 e))
in (_126_900)::p))))
end
| _47_1730 -> begin
(
# 1078 "FStar.ToSMT.Encode.fst"
let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (let _126_906 = (FStar_ToSMT_Term.mk_Precedes tl e)
in (_126_906)::p))))
end
| (x, FStar_ToSMT_Term.Term_sort)::vars -> begin
(let _126_908 = (let _126_907 = (FStar_ToSMT_Term.mkFreeV (x, FStar_ToSMT_Term.Term_sort))
in (FStar_ToSMT_Term.mk_LexCons _126_907 tl))
in (aux _126_908 vars))
end
| _47_1742 -> begin
pats
end))
in (let _126_909 = (FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", FStar_ToSMT_Term.Term_sort))
in (aux _126_909 vars)))
end)
end)
in (
# 1085 "FStar.ToSMT.Encode.fst"
let env = (
# 1085 "FStar.ToSMT.Encode.fst"
let _47_1744 = env
in {bindings = _47_1744.bindings; depth = _47_1744.depth; tcenv = _47_1744.tcenv; warn = _47_1744.warn; cache = _47_1744.cache; nolabels = true; use_zfuel_name = _47_1744.use_zfuel_name; encode_non_total_function_typ = _47_1744.encode_non_total_function_typ})
in (
# 1086 "FStar.ToSMT.Encode.fst"
let _47_1749 = (let _126_910 = (FStar_Absyn_Util.unmeta_typ pre)
in (encode_formula _126_910 env))
in (match (_47_1749) with
| (pre, decls'') -> begin
(
# 1087 "FStar.ToSMT.Encode.fst"
let _47_1752 = (let _126_911 = (FStar_Absyn_Util.unmeta_typ post)
in (encode_formula _126_911 env))
in (match (_47_1752) with
| (post, decls''') -> begin
(
# 1088 "FStar.ToSMT.Encode.fst"
let decls = (FStar_List.append (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'') decls''')
in (let _126_916 = (let _126_915 = (let _126_914 = (let _126_913 = (let _126_912 = (FStar_ToSMT_Term.mk_and_l ((pre)::guards))
in (_126_912, post))
in (FStar_ToSMT_Term.mkImp _126_913))
in (pats, vars, _126_914))
in (FStar_ToSMT_Term.mkForall _126_915))
in (_126_916, decls)))
end))
end)))))
end))
end))
end))))))
and encode_formula_with_labels : FStar_Absyn_Syntax.typ  ->  env_t  ->  (FStar_ToSMT_Term.term * labels * FStar_ToSMT_Term.decls_t) = (fun phi env -> (
# 1092 "FStar.ToSMT.Encode.fst"
let enc = (fun f l -> (
# 1093 "FStar.ToSMT.Encode.fst"
let _47_1773 = (FStar_Util.fold_map (fun decls x -> (match ((Prims.fst x)) with
| FStar_Util.Inl (t) -> begin
(
# 1094 "FStar.ToSMT.Encode.fst"
let _47_1765 = (encode_typ_term t env)
in (match (_47_1765) with
| (t, decls') -> begin
((FStar_List.append decls decls'), t)
end))
end
| FStar_Util.Inr (e) -> begin
(
# 1095 "FStar.ToSMT.Encode.fst"
let _47_1770 = (encode_exp e env)
in (match (_47_1770) with
| (e, decls') -> begin
((FStar_List.append decls decls'), e)
end))
end)) [] l)
in (match (_47_1773) with
| (decls, args) -> begin
(let _126_934 = (f args)
in (_126_934, [], decls))
end)))
in (
# 1098 "FStar.ToSMT.Encode.fst"
let enc_prop_c = (fun f l -> (
# 1099 "FStar.ToSMT.Encode.fst"
let _47_1793 = (FStar_List.fold_right (fun t _47_1781 -> (match (_47_1781) with
| (phis, labs, decls) -> begin
(match ((Prims.fst t)) with
| FStar_Util.Inl (t) -> begin
(
# 1103 "FStar.ToSMT.Encode.fst"
let _47_1787 = (encode_formula_with_labels t env)
in (match (_47_1787) with
| (phi, labs', decls') -> begin
((phi)::phis, (FStar_List.append labs' labs), (FStar_List.append decls' decls))
end))
end
| _47_1789 -> begin
(FStar_All.failwith "Expected a formula")
end)
end)) l ([], [], []))
in (match (_47_1793) with
| (phis, labs, decls) -> begin
(let _126_950 = (f phis)
in (_126_950, labs, decls))
end)))
in (
# 1110 "FStar.ToSMT.Encode.fst"
let const_op = (fun f _47_1796 -> (f, [], []))
in (
# 1111 "FStar.ToSMT.Encode.fst"
let un_op = (fun f l -> (let _126_964 = (FStar_List.hd l)
in (FStar_All.pipe_left f _126_964)))
in (
# 1112 "FStar.ToSMT.Encode.fst"
let bin_op = (fun f _47_13 -> (match (_47_13) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _47_1807 -> begin
(FStar_All.failwith "Impossible")
end))
in (
# 1115 "FStar.ToSMT.Encode.fst"
let eq_op = (fun _47_14 -> (match (_47_14) with
| _47_1815::_47_1813::e1::e2::[] -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op FStar_ToSMT_Term.mkEq) l)
end))
in (
# 1119 "FStar.ToSMT.Encode.fst"
let mk_imp = (fun _47_15 -> (match (_47_15) with
| (FStar_Util.Inl (lhs), _47_1828)::(FStar_Util.Inl (rhs), _47_1823)::[] -> begin
(
# 1121 "FStar.ToSMT.Encode.fst"
let _47_1834 = (encode_formula_with_labels rhs env)
in (match (_47_1834) with
| (l1, labs1, decls1) -> begin
(match (l1.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _47_1837) -> begin
(l1, labs1, decls1)
end
| _47_1841 -> begin
(
# 1125 "FStar.ToSMT.Encode.fst"
let _47_1845 = (encode_formula_with_labels lhs env)
in (match (_47_1845) with
| (l2, labs2, decls2) -> begin
(let _126_978 = (FStar_ToSMT_Term.mkImp (l2, l1))
in (_126_978, (FStar_List.append labs1 labs2), (FStar_List.append decls1 decls2)))
end))
end)
end))
end
| _47_1847 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1130 "FStar.ToSMT.Encode.fst"
let mk_ite = (fun _47_16 -> (match (_47_16) with
| (FStar_Util.Inl (guard), _47_1863)::(FStar_Util.Inl (_then), _47_1858)::(FStar_Util.Inl (_else), _47_1853)::[] -> begin
(
# 1132 "FStar.ToSMT.Encode.fst"
let _47_1869 = (encode_formula_with_labels guard env)
in (match (_47_1869) with
| (g, labs1, decls1) -> begin
(
# 1133 "FStar.ToSMT.Encode.fst"
let _47_1873 = (encode_formula_with_labels _then env)
in (match (_47_1873) with
| (t, labs2, decls2) -> begin
(
# 1134 "FStar.ToSMT.Encode.fst"
let _47_1877 = (encode_formula_with_labels _else env)
in (match (_47_1877) with
| (e, labs3, decls3) -> begin
(
# 1135 "FStar.ToSMT.Encode.fst"
let res = (FStar_ToSMT_Term.mkITE (g, t, e))
in (res, (FStar_List.append (FStar_List.append labs1 labs2) labs3), (FStar_List.append (FStar_List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _47_1880 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1140 "FStar.ToSMT.Encode.fst"
let unboxInt_l = (fun f l -> (let _126_990 = (FStar_List.map FStar_ToSMT_Term.unboxInt l)
in (f _126_990)))
in (
# 1141 "FStar.ToSMT.Encode.fst"
let connectives = (let _126_1051 = (let _126_999 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkAnd))
in (FStar_Absyn_Const.and_lid, _126_999))
in (let _126_1050 = (let _126_1049 = (let _126_1005 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkOr))
in (FStar_Absyn_Const.or_lid, _126_1005))
in (let _126_1048 = (let _126_1047 = (let _126_1046 = (let _126_1014 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_ToSMT_Term.mkIff))
in (FStar_Absyn_Const.iff_lid, _126_1014))
in (let _126_1045 = (let _126_1044 = (let _126_1043 = (let _126_1023 = (FStar_All.pipe_left enc_prop_c (un_op FStar_ToSMT_Term.mkNot))
in (FStar_Absyn_Const.not_lid, _126_1023))
in (let _126_1042 = (let _126_1041 = (let _126_1029 = (FStar_All.pipe_left enc (bin_op FStar_ToSMT_Term.mkEq))
in (FStar_Absyn_Const.eqT_lid, _126_1029))
in (_126_1041)::((FStar_Absyn_Const.eq2_lid, eq_op))::((FStar_Absyn_Const.true_lid, (const_op FStar_ToSMT_Term.mkTrue)))::((FStar_Absyn_Const.false_lid, (const_op FStar_ToSMT_Term.mkFalse)))::[])
in (_126_1043)::_126_1042))
in ((FStar_Absyn_Const.ite_lid, mk_ite))::_126_1044)
in (_126_1046)::_126_1045))
in ((FStar_Absyn_Const.imp_lid, mk_imp))::_126_1047)
in (_126_1049)::_126_1048))
in (_126_1051)::_126_1050))
in (
# 1154 "FStar.ToSMT.Encode.fst"
let fallback = (fun phi -> (match (phi.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_meta (FStar_Absyn_Syntax.Meta_labeled (phi', msg, r, b)) -> begin
(
# 1156 "FStar.ToSMT.Encode.fst"
let _47_1898 = (encode_formula_with_labels phi' env)
in (match (_47_1898) with
| (phi, labs, decls) -> begin
if env.nolabels then begin
(phi, [], decls)
end else begin
(
# 1159 "FStar.ToSMT.Encode.fst"
let lvar = (let _126_1054 = (varops.fresh "label")
in (_126_1054, FStar_ToSMT_Term.Bool_sort))
in (
# 1160 "FStar.ToSMT.Encode.fst"
let lterm = (FStar_ToSMT_Term.mkFreeV lvar)
in (
# 1161 "FStar.ToSMT.Encode.fst"
let lphi = (FStar_ToSMT_Term.mkOr (lterm, phi))
in (lphi, ((lvar, msg, r))::labs, decls))))
end
end))
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _47_1909; FStar_Absyn_Syntax.pos = _47_1907; FStar_Absyn_Syntax.fvs = _47_1905; FStar_Absyn_Syntax.uvs = _47_1903}, _47_1924::(FStar_Util.Inr (l), _47_1921)::(FStar_Util.Inl (phi), _47_1916)::[]) when (FStar_Ident.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_IH) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(
# 1166 "FStar.ToSMT.Encode.fst"
let _47_1930 = (encode_exp l env)
in (match (_47_1930) with
| (e, decls) -> begin
(
# 1167 "FStar.ToSMT.Encode.fst"
let _47_1933 = (encode_function_type_as_formula (Some (e)) None phi env)
in (match (_47_1933) with
| (f, decls') -> begin
(f, [], (FStar_List.append decls decls'))
end))
end))
end else begin
(FStar_ToSMT_Term.mkTrue, [], [])
end
end
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ih); FStar_Absyn_Syntax.tk = _47_1941; FStar_Absyn_Syntax.pos = _47_1939; FStar_Absyn_Syntax.fvs = _47_1937; FStar_Absyn_Syntax.uvs = _47_1935}, _47_1953::(FStar_Util.Inl (phi), _47_1949)::tl) when (FStar_Ident.lid_equals ih.FStar_Absyn_Syntax.v FStar_Absyn_Const.using_lem) -> begin
if (FStar_Absyn_Util.is_lemma phi) then begin
(
# 1174 "FStar.ToSMT.Encode.fst"
let pat = (match (tl) with
| [] -> begin
None
end
| (FStar_Util.Inr (pat), _47_1961)::[] -> begin
Some (pat)
end)
in (
# 1177 "FStar.ToSMT.Encode.fst"
let _47_1967 = (encode_function_type_as_formula None pat phi env)
in (match (_47_1967) with
| (f, decls) -> begin
(f, [], decls)
end)))
end else begin
(FStar_ToSMT_Term.mkTrue, [], [])
end
end
| _47_1969 -> begin
(
# 1182 "FStar.ToSMT.Encode.fst"
let _47_1972 = (encode_typ_term phi env)
in (match (_47_1972) with
| (tt, decls) -> begin
(let _126_1055 = (FStar_ToSMT_Term.mk_Valid tt)
in (_126_1055, [], decls))
end))
end))
in (
# 1185 "FStar.ToSMT.Encode.fst"
let encode_q_body = (fun env bs ps body -> (
# 1186 "FStar.ToSMT.Encode.fst"
let _47_1984 = (encode_binders None bs env)
in (match (_47_1984) with
| (vars, guards, env, decls, _47_1983) -> begin
(
# 1187 "FStar.ToSMT.Encode.fst"
let _47_2004 = (let _126_1067 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (
# 1188 "FStar.ToSMT.Encode.fst"
let _47_2001 = (let _126_1066 = (FStar_All.pipe_right p (FStar_List.map (fun _47_17 -> (match (_47_17) with
| (FStar_Util.Inl (t), _47_1990) -> begin
(encode_typ_term t env)
end
| (FStar_Util.Inr (e), _47_1995) -> begin
(encode_exp e (
# 1190 "FStar.ToSMT.Encode.fst"
let _47_1997 = env
in {bindings = _47_1997.bindings; depth = _47_1997.depth; tcenv = _47_1997.tcenv; warn = _47_1997.warn; cache = _47_1997.cache; nolabels = _47_1997.nolabels; use_zfuel_name = true; encode_non_total_function_typ = _47_1997.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right _126_1066 FStar_List.unzip))
in (match (_47_2001) with
| (p, decls) -> begin
(p, (FStar_List.flatten decls))
end)))))
in (FStar_All.pipe_right _126_1067 FStar_List.unzip))
in (match (_47_2004) with
| (pats, decls') -> begin
(
# 1192 "FStar.ToSMT.Encode.fst"
let _47_2008 = (encode_formula_with_labels body env)
in (match (_47_2008) with
| (body, labs, decls'') -> begin
(let _126_1068 = (FStar_ToSMT_Term.mk_and_l guards)
in (vars, pats, _126_1068, body, labs, (FStar_List.append (FStar_List.append decls (FStar_List.flatten decls')) decls'')))
end))
end))
end)))
in (
# 1195 "FStar.ToSMT.Encode.fst"
let _47_2009 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _126_1069 = (FStar_Absyn_Print.formula_to_string phi)
in (FStar_Util.print1 ">>>> Destructing as formula ... %s\n" _126_1069))
end else begin
()
end
in (
# 1197 "FStar.ToSMT.Encode.fst"
let phi = (FStar_Absyn_Util.compress_typ phi)
in (match ((FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (FStar_Absyn_Util.BaseConn (op, arms)) -> begin
(match ((FStar_All.pipe_right connectives (FStar_List.tryFind (fun _47_2021 -> (match (_47_2021) with
| (l, _47_2020) -> begin
(FStar_Ident.lid_equals op l)
end))))) with
| None -> begin
(fallback phi)
end
| Some (_47_2024, f) -> begin
(f arms)
end)
end
| Some (FStar_Absyn_Util.QAll (vars, pats, body)) -> begin
(
# 1207 "FStar.ToSMT.Encode.fst"
let _47_2034 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _126_1086 = (FStar_All.pipe_right vars (FStar_Absyn_Print.binders_to_string "; "))
in (FStar_Util.print1 ">>>> Got QALL [%s]\n" _126_1086))
end else begin
()
end
in (
# 1210 "FStar.ToSMT.Encode.fst"
let _47_2042 = (encode_q_body env vars pats body)
in (match (_47_2042) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _126_1089 = (let _126_1088 = (let _126_1087 = (FStar_ToSMT_Term.mkImp (guard, body))
in (pats, vars, _126_1087))
in (FStar_ToSMT_Term.mkForall _126_1088))
in (_126_1089, labs, decls))
end)))
end
| Some (FStar_Absyn_Util.QEx (vars, pats, body)) -> begin
(
# 1214 "FStar.ToSMT.Encode.fst"
let _47_2055 = (encode_q_body env vars pats body)
in (match (_47_2055) with
| (vars, pats, guard, body, labs, decls) -> begin
(let _126_1092 = (let _126_1091 = (let _126_1090 = (FStar_ToSMT_Term.mkAnd (guard, body))
in (pats, vars, _126_1090))
in (FStar_ToSMT_Term.mkExists _126_1091))
in (_126_1092, labs, decls))
end))
end))))))))))))))))

# 1223 "FStar.ToSMT.Encode.fst"
type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.decl Prims.list; is : FStar_Ident.lident  ->  Prims.bool}

# 1223 "FStar.ToSMT.Encode.fst"
let is_Mkprims_t : prims_t  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkprims_t"))))

# 1229 "FStar.ToSMT.Encode.fst"
let prims : prims_t = (
# 1230 "FStar.ToSMT.Encode.fst"
let _47_2061 = (fresh_fvar "a" FStar_ToSMT_Term.Type_sort)
in (match (_47_2061) with
| (asym, a) -> begin
(
# 1231 "FStar.ToSMT.Encode.fst"
let _47_2064 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_47_2064) with
| (xsym, x) -> begin
(
# 1232 "FStar.ToSMT.Encode.fst"
let _47_2067 = (fresh_fvar "y" FStar_ToSMT_Term.Term_sort)
in (match (_47_2067) with
| (ysym, y) -> begin
(
# 1233 "FStar.ToSMT.Encode.fst"
let deffun = (fun vars body x -> (let _126_1127 = (let _126_1126 = (let _126_1125 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (let _126_1124 = (FStar_ToSMT_Term.abstr vars body)
in (x, _126_1125, FStar_ToSMT_Term.Term_sort, _126_1124, None)))
in FStar_ToSMT_Term.DefineFun (_126_1126))
in (_126_1127)::[]))
in (
# 1235 "FStar.ToSMT.Encode.fst"
let quant = (fun vars body x -> (
# 1236 "FStar.ToSMT.Encode.fst"
let t1 = (let _126_1139 = (let _126_1138 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (x, _126_1138))
in (FStar_ToSMT_Term.mkApp _126_1139))
in (
# 1237 "FStar.ToSMT.Encode.fst"
let vname_decl = (let _126_1141 = (let _126_1140 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (x, _126_1140, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_126_1141))
in (let _126_1147 = (let _126_1146 = (let _126_1145 = (let _126_1144 = (let _126_1143 = (let _126_1142 = (FStar_ToSMT_Term.mkEq (t1, body))
in (((t1)::[])::[], vars, _126_1142))
in (FStar_ToSMT_Term.mkForall _126_1143))
in (_126_1144, None))
in FStar_ToSMT_Term.Assume (_126_1145))
in (_126_1146)::[])
in (vname_decl)::_126_1147))))
in (
# 1240 "FStar.ToSMT.Encode.fst"
let def_or_quant = (fun vars body x -> if (FStar_ST.read FStar_Options.inline_arith) then begin
(deffun vars body x)
end else begin
(quant vars body x)
end)
in (
# 1244 "FStar.ToSMT.Encode.fst"
let axy = ((asym, FStar_ToSMT_Term.Type_sort))::((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (
# 1245 "FStar.ToSMT.Encode.fst"
let xy = ((xsym, FStar_ToSMT_Term.Term_sort))::((ysym, FStar_ToSMT_Term.Term_sort))::[]
in (
# 1246 "FStar.ToSMT.Encode.fst"
let qx = ((xsym, FStar_ToSMT_Term.Term_sort))::[]
in (
# 1247 "FStar.ToSMT.Encode.fst"
let prims = (let _126_1313 = (let _126_1162 = (let _126_1161 = (let _126_1160 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _126_1160))
in (def_or_quant axy _126_1161))
in (FStar_Absyn_Const.op_Eq, _126_1162))
in (let _126_1312 = (let _126_1311 = (let _126_1169 = (let _126_1168 = (let _126_1167 = (let _126_1166 = (FStar_ToSMT_Term.mkEq (x, y))
in (FStar_ToSMT_Term.mkNot _126_1166))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _126_1167))
in (def_or_quant axy _126_1168))
in (FStar_Absyn_Const.op_notEq, _126_1169))
in (let _126_1310 = (let _126_1309 = (let _126_1178 = (let _126_1177 = (let _126_1176 = (let _126_1175 = (let _126_1174 = (FStar_ToSMT_Term.unboxInt x)
in (let _126_1173 = (FStar_ToSMT_Term.unboxInt y)
in (_126_1174, _126_1173)))
in (FStar_ToSMT_Term.mkLT _126_1175))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _126_1176))
in (def_or_quant xy _126_1177))
in (FStar_Absyn_Const.op_LT, _126_1178))
in (let _126_1308 = (let _126_1307 = (let _126_1187 = (let _126_1186 = (let _126_1185 = (let _126_1184 = (let _126_1183 = (FStar_ToSMT_Term.unboxInt x)
in (let _126_1182 = (FStar_ToSMT_Term.unboxInt y)
in (_126_1183, _126_1182)))
in (FStar_ToSMT_Term.mkLTE _126_1184))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _126_1185))
in (def_or_quant xy _126_1186))
in (FStar_Absyn_Const.op_LTE, _126_1187))
in (let _126_1306 = (let _126_1305 = (let _126_1196 = (let _126_1195 = (let _126_1194 = (let _126_1193 = (let _126_1192 = (FStar_ToSMT_Term.unboxInt x)
in (let _126_1191 = (FStar_ToSMT_Term.unboxInt y)
in (_126_1192, _126_1191)))
in (FStar_ToSMT_Term.mkGT _126_1193))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _126_1194))
in (def_or_quant xy _126_1195))
in (FStar_Absyn_Const.op_GT, _126_1196))
in (let _126_1304 = (let _126_1303 = (let _126_1205 = (let _126_1204 = (let _126_1203 = (let _126_1202 = (let _126_1201 = (FStar_ToSMT_Term.unboxInt x)
in (let _126_1200 = (FStar_ToSMT_Term.unboxInt y)
in (_126_1201, _126_1200)))
in (FStar_ToSMT_Term.mkGTE _126_1202))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _126_1203))
in (def_or_quant xy _126_1204))
in (FStar_Absyn_Const.op_GTE, _126_1205))
in (let _126_1302 = (let _126_1301 = (let _126_1214 = (let _126_1213 = (let _126_1212 = (let _126_1211 = (let _126_1210 = (FStar_ToSMT_Term.unboxInt x)
in (let _126_1209 = (FStar_ToSMT_Term.unboxInt y)
in (_126_1210, _126_1209)))
in (FStar_ToSMT_Term.mkSub _126_1211))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _126_1212))
in (def_or_quant xy _126_1213))
in (FStar_Absyn_Const.op_Subtraction, _126_1214))
in (let _126_1300 = (let _126_1299 = (let _126_1221 = (let _126_1220 = (let _126_1219 = (let _126_1218 = (FStar_ToSMT_Term.unboxInt x)
in (FStar_ToSMT_Term.mkMinus _126_1218))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _126_1219))
in (def_or_quant qx _126_1220))
in (FStar_Absyn_Const.op_Minus, _126_1221))
in (let _126_1298 = (let _126_1297 = (let _126_1230 = (let _126_1229 = (let _126_1228 = (let _126_1227 = (let _126_1226 = (FStar_ToSMT_Term.unboxInt x)
in (let _126_1225 = (FStar_ToSMT_Term.unboxInt y)
in (_126_1226, _126_1225)))
in (FStar_ToSMT_Term.mkAdd _126_1227))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _126_1228))
in (def_or_quant xy _126_1229))
in (FStar_Absyn_Const.op_Addition, _126_1230))
in (let _126_1296 = (let _126_1295 = (let _126_1239 = (let _126_1238 = (let _126_1237 = (let _126_1236 = (let _126_1235 = (FStar_ToSMT_Term.unboxInt x)
in (let _126_1234 = (FStar_ToSMT_Term.unboxInt y)
in (_126_1235, _126_1234)))
in (FStar_ToSMT_Term.mkMul _126_1236))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _126_1237))
in (def_or_quant xy _126_1238))
in (FStar_Absyn_Const.op_Multiply, _126_1239))
in (let _126_1294 = (let _126_1293 = (let _126_1248 = (let _126_1247 = (let _126_1246 = (let _126_1245 = (let _126_1244 = (FStar_ToSMT_Term.unboxInt x)
in (let _126_1243 = (FStar_ToSMT_Term.unboxInt y)
in (_126_1244, _126_1243)))
in (FStar_ToSMT_Term.mkDiv _126_1245))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _126_1246))
in (def_or_quant xy _126_1247))
in (FStar_Absyn_Const.op_Division, _126_1248))
in (let _126_1292 = (let _126_1291 = (let _126_1257 = (let _126_1256 = (let _126_1255 = (let _126_1254 = (let _126_1253 = (FStar_ToSMT_Term.unboxInt x)
in (let _126_1252 = (FStar_ToSMT_Term.unboxInt y)
in (_126_1253, _126_1252)))
in (FStar_ToSMT_Term.mkMod _126_1254))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxInt _126_1255))
in (def_or_quant xy _126_1256))
in (FStar_Absyn_Const.op_Modulus, _126_1257))
in (let _126_1290 = (let _126_1289 = (let _126_1266 = (let _126_1265 = (let _126_1264 = (let _126_1263 = (let _126_1262 = (FStar_ToSMT_Term.unboxBool x)
in (let _126_1261 = (FStar_ToSMT_Term.unboxBool y)
in (_126_1262, _126_1261)))
in (FStar_ToSMT_Term.mkAnd _126_1263))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _126_1264))
in (def_or_quant xy _126_1265))
in (FStar_Absyn_Const.op_And, _126_1266))
in (let _126_1288 = (let _126_1287 = (let _126_1275 = (let _126_1274 = (let _126_1273 = (let _126_1272 = (let _126_1271 = (FStar_ToSMT_Term.unboxBool x)
in (let _126_1270 = (FStar_ToSMT_Term.unboxBool y)
in (_126_1271, _126_1270)))
in (FStar_ToSMT_Term.mkOr _126_1272))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _126_1273))
in (def_or_quant xy _126_1274))
in (FStar_Absyn_Const.op_Or, _126_1275))
in (let _126_1286 = (let _126_1285 = (let _126_1282 = (let _126_1281 = (let _126_1280 = (let _126_1279 = (FStar_ToSMT_Term.unboxBool x)
in (FStar_ToSMT_Term.mkNot _126_1279))
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _126_1280))
in (def_or_quant qx _126_1281))
in (FStar_Absyn_Const.op_Negation, _126_1282))
in (_126_1285)::[])
in (_126_1287)::_126_1286))
in (_126_1289)::_126_1288))
in (_126_1291)::_126_1290))
in (_126_1293)::_126_1292))
in (_126_1295)::_126_1294))
in (_126_1297)::_126_1296))
in (_126_1299)::_126_1298))
in (_126_1301)::_126_1300))
in (_126_1303)::_126_1302))
in (_126_1305)::_126_1304))
in (_126_1307)::_126_1306))
in (_126_1309)::_126_1308))
in (_126_1311)::_126_1310))
in (_126_1313)::_126_1312))
in (
# 1264 "FStar.ToSMT.Encode.fst"
let mk = (fun l v -> (let _126_1345 = (FStar_All.pipe_right prims (FStar_List.filter (fun _47_2091 -> (match (_47_2091) with
| (l', _47_2090) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right _126_1345 (FStar_List.collect (fun _47_2095 -> (match (_47_2095) with
| (_47_2093, b) -> begin
(b v)
end))))))
in (
# 1266 "FStar.ToSMT.Encode.fst"
let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun _47_2101 -> (match (_47_2101) with
| (l', _47_2100) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))))
end))
end))
end))

# 1271 "FStar.ToSMT.Encode.fst"
let primitive_type_axioms : FStar_Ident.lident  ->  Prims.string  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.decl Prims.list = (
# 1272 "FStar.ToSMT.Encode.fst"
let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (
# 1273 "FStar.ToSMT.Encode.fst"
let x = (FStar_ToSMT_Term.mkFreeV xx)
in (
# 1275 "FStar.ToSMT.Encode.fst"
let yy = ("y", FStar_ToSMT_Term.Term_sort)
in (
# 1276 "FStar.ToSMT.Encode.fst"
let y = (FStar_ToSMT_Term.mkFreeV yy)
in (
# 1278 "FStar.ToSMT.Encode.fst"
let mk_unit = (fun _47_2107 tt -> (
# 1279 "FStar.ToSMT.Encode.fst"
let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (let _126_1377 = (let _126_1368 = (let _126_1367 = (FStar_ToSMT_Term.mk_HasType FStar_ToSMT_Term.mk_Term_unit tt)
in (_126_1367, Some ("unit typing")))
in FStar_ToSMT_Term.Assume (_126_1368))
in (let _126_1376 = (let _126_1375 = (let _126_1374 = (let _126_1373 = (let _126_1372 = (let _126_1371 = (let _126_1370 = (let _126_1369 = (FStar_ToSMT_Term.mkEq (x, FStar_ToSMT_Term.mk_Term_unit))
in (typing_pred, _126_1369))
in (FStar_ToSMT_Term.mkImp _126_1370))
in (((typing_pred)::[])::[], (xx)::[], _126_1371))
in (mkForall_fuel _126_1372))
in (_126_1373, Some ("unit inversion")))
in FStar_ToSMT_Term.Assume (_126_1374))
in (_126_1375)::[])
in (_126_1377)::_126_1376))))
in (
# 1282 "FStar.ToSMT.Encode.fst"
let mk_bool = (fun _47_2112 tt -> (
# 1283 "FStar.ToSMT.Encode.fst"
let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (
# 1284 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Bool_sort)
in (
# 1285 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _126_1398 = (let _126_1387 = (let _126_1386 = (let _126_1385 = (let _126_1384 = (let _126_1383 = (let _126_1382 = (FStar_ToSMT_Term.mk_tester "BoxBool" x)
in (typing_pred, _126_1382))
in (FStar_ToSMT_Term.mkImp _126_1383))
in (((typing_pred)::[])::[], (xx)::[], _126_1384))
in (mkForall_fuel _126_1385))
in (_126_1386, Some ("bool inversion")))
in FStar_ToSMT_Term.Assume (_126_1387))
in (let _126_1397 = (let _126_1396 = (let _126_1395 = (let _126_1394 = (let _126_1393 = (let _126_1392 = (let _126_1389 = (let _126_1388 = (FStar_ToSMT_Term.boxBool b)
in (_126_1388)::[])
in (_126_1389)::[])
in (let _126_1391 = (let _126_1390 = (FStar_ToSMT_Term.boxBool b)
in (FStar_ToSMT_Term.mk_HasType _126_1390 tt))
in (_126_1392, (bb)::[], _126_1391)))
in (FStar_ToSMT_Term.mkForall _126_1393))
in (_126_1394, Some ("bool typing")))
in FStar_ToSMT_Term.Assume (_126_1395))
in (_126_1396)::[])
in (_126_1398)::_126_1397))))))
in (
# 1288 "FStar.ToSMT.Encode.fst"
let mk_int = (fun _47_2119 tt -> (
# 1289 "FStar.ToSMT.Encode.fst"
let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (
# 1290 "FStar.ToSMT.Encode.fst"
let typing_pred_y = (FStar_ToSMT_Term.mk_HasType y tt)
in (
# 1291 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Int_sort)
in (
# 1292 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1293 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Int_sort)
in (
# 1294 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1295 "FStar.ToSMT.Encode.fst"
let precedes = (let _126_1410 = (let _126_1409 = (let _126_1408 = (let _126_1407 = (let _126_1406 = (let _126_1405 = (FStar_ToSMT_Term.boxInt a)
in (let _126_1404 = (let _126_1403 = (FStar_ToSMT_Term.boxInt b)
in (_126_1403)::[])
in (_126_1405)::_126_1404))
in (tt)::_126_1406)
in (tt)::_126_1407)
in ("Prims.Precedes", _126_1408))
in (FStar_ToSMT_Term.mkApp _126_1409))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _126_1410))
in (
# 1296 "FStar.ToSMT.Encode.fst"
let precedes_y_x = (let _126_1411 = (FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[]))
in (FStar_All.pipe_left FStar_ToSMT_Term.mk_Valid _126_1411))
in (let _126_1453 = (let _126_1417 = (let _126_1416 = (let _126_1415 = (let _126_1414 = (let _126_1413 = (let _126_1412 = (FStar_ToSMT_Term.mk_tester "BoxInt" x)
in (typing_pred, _126_1412))
in (FStar_ToSMT_Term.mkImp _126_1413))
in (((typing_pred)::[])::[], (xx)::[], _126_1414))
in (mkForall_fuel _126_1415))
in (_126_1416, Some ("int inversion")))
in FStar_ToSMT_Term.Assume (_126_1417))
in (let _126_1452 = (let _126_1451 = (let _126_1425 = (let _126_1424 = (let _126_1423 = (let _126_1422 = (let _126_1419 = (let _126_1418 = (FStar_ToSMT_Term.boxInt b)
in (_126_1418)::[])
in (_126_1419)::[])
in (let _126_1421 = (let _126_1420 = (FStar_ToSMT_Term.boxInt b)
in (FStar_ToSMT_Term.mk_HasType _126_1420 tt))
in (_126_1422, (bb)::[], _126_1421)))
in (FStar_ToSMT_Term.mkForall _126_1423))
in (_126_1424, Some ("int typing")))
in FStar_ToSMT_Term.Assume (_126_1425))
in (let _126_1450 = (let _126_1449 = (let _126_1448 = (let _126_1447 = (let _126_1446 = (let _126_1445 = (let _126_1444 = (let _126_1443 = (let _126_1442 = (let _126_1441 = (let _126_1440 = (let _126_1439 = (let _126_1428 = (let _126_1427 = (FStar_ToSMT_Term.unboxInt x)
in (let _126_1426 = (FStar_ToSMT_Term.mkInteger' 0)
in (_126_1427, _126_1426)))
in (FStar_ToSMT_Term.mkGT _126_1428))
in (let _126_1438 = (let _126_1437 = (let _126_1431 = (let _126_1430 = (FStar_ToSMT_Term.unboxInt y)
in (let _126_1429 = (FStar_ToSMT_Term.mkInteger' 0)
in (_126_1430, _126_1429)))
in (FStar_ToSMT_Term.mkGTE _126_1431))
in (let _126_1436 = (let _126_1435 = (let _126_1434 = (let _126_1433 = (FStar_ToSMT_Term.unboxInt y)
in (let _126_1432 = (FStar_ToSMT_Term.unboxInt x)
in (_126_1433, _126_1432)))
in (FStar_ToSMT_Term.mkLT _126_1434))
in (_126_1435)::[])
in (_126_1437)::_126_1436))
in (_126_1439)::_126_1438))
in (typing_pred_y)::_126_1440)
in (typing_pred)::_126_1441)
in (FStar_ToSMT_Term.mk_and_l _126_1442))
in (_126_1443, precedes_y_x))
in (FStar_ToSMT_Term.mkImp _126_1444))
in (((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[], (xx)::(yy)::[], _126_1445))
in (mkForall_fuel _126_1446))
in (_126_1447, Some ("well-founded ordering on nat (alt)")))
in FStar_ToSMT_Term.Assume (_126_1448))
in (_126_1449)::[])
in (_126_1451)::_126_1450))
in (_126_1453)::_126_1452)))))))))))
in (
# 1308 "FStar.ToSMT.Encode.fst"
let mk_int_alias = (fun _47_2131 tt -> (let _126_1462 = (let _126_1461 = (let _126_1460 = (let _126_1459 = (let _126_1458 = (FStar_ToSMT_Term.mkApp (FStar_Absyn_Const.int_lid.FStar_Ident.str, []))
in (tt, _126_1458))
in (FStar_ToSMT_Term.mkEq _126_1459))
in (_126_1460, Some ("mapping to int; for now")))
in FStar_ToSMT_Term.Assume (_126_1461))
in (_126_1462)::[]))
in (
# 1310 "FStar.ToSMT.Encode.fst"
let mk_str = (fun _47_2135 tt -> (
# 1311 "FStar.ToSMT.Encode.fst"
let typing_pred = (FStar_ToSMT_Term.mk_HasType x tt)
in (
# 1312 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.String_sort)
in (
# 1313 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (let _126_1483 = (let _126_1472 = (let _126_1471 = (let _126_1470 = (let _126_1469 = (let _126_1468 = (let _126_1467 = (FStar_ToSMT_Term.mk_tester "BoxString" x)
in (typing_pred, _126_1467))
in (FStar_ToSMT_Term.mkImp _126_1468))
in (((typing_pred)::[])::[], (xx)::[], _126_1469))
in (mkForall_fuel _126_1470))
in (_126_1471, Some ("string inversion")))
in FStar_ToSMT_Term.Assume (_126_1472))
in (let _126_1482 = (let _126_1481 = (let _126_1480 = (let _126_1479 = (let _126_1478 = (let _126_1477 = (let _126_1474 = (let _126_1473 = (FStar_ToSMT_Term.boxString b)
in (_126_1473)::[])
in (_126_1474)::[])
in (let _126_1476 = (let _126_1475 = (FStar_ToSMT_Term.boxString b)
in (FStar_ToSMT_Term.mk_HasType _126_1475 tt))
in (_126_1477, (bb)::[], _126_1476)))
in (FStar_ToSMT_Term.mkForall _126_1478))
in (_126_1479, Some ("string typing")))
in FStar_ToSMT_Term.Assume (_126_1480))
in (_126_1481)::[])
in (_126_1483)::_126_1482))))))
in (
# 1316 "FStar.ToSMT.Encode.fst"
let mk_ref = (fun reft_name _47_2143 -> (
# 1317 "FStar.ToSMT.Encode.fst"
let r = ("r", FStar_ToSMT_Term.Ref_sort)
in (
# 1318 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (
# 1319 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (
# 1320 "FStar.ToSMT.Encode.fst"
let refa = (let _126_1490 = (let _126_1489 = (let _126_1488 = (FStar_ToSMT_Term.mkFreeV aa)
in (_126_1488)::[])
in (reft_name, _126_1489))
in (FStar_ToSMT_Term.mkApp _126_1490))
in (
# 1321 "FStar.ToSMT.Encode.fst"
let refb = (let _126_1493 = (let _126_1492 = (let _126_1491 = (FStar_ToSMT_Term.mkFreeV bb)
in (_126_1491)::[])
in (reft_name, _126_1492))
in (FStar_ToSMT_Term.mkApp _126_1493))
in (
# 1322 "FStar.ToSMT.Encode.fst"
let typing_pred = (FStar_ToSMT_Term.mk_HasType x refa)
in (
# 1323 "FStar.ToSMT.Encode.fst"
let typing_pred_b = (FStar_ToSMT_Term.mk_HasType x refb)
in (let _126_1512 = (let _126_1499 = (let _126_1498 = (let _126_1497 = (let _126_1496 = (let _126_1495 = (let _126_1494 = (FStar_ToSMT_Term.mk_tester "BoxRef" x)
in (typing_pred, _126_1494))
in (FStar_ToSMT_Term.mkImp _126_1495))
in (((typing_pred)::[])::[], (xx)::(aa)::[], _126_1496))
in (mkForall_fuel _126_1497))
in (_126_1498, Some ("ref inversion")))
in FStar_ToSMT_Term.Assume (_126_1499))
in (let _126_1511 = (let _126_1510 = (let _126_1509 = (let _126_1508 = (let _126_1507 = (let _126_1506 = (let _126_1505 = (let _126_1504 = (FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b))
in (let _126_1503 = (let _126_1502 = (let _126_1501 = (FStar_ToSMT_Term.mkFreeV aa)
in (let _126_1500 = (FStar_ToSMT_Term.mkFreeV bb)
in (_126_1501, _126_1500)))
in (FStar_ToSMT_Term.mkEq _126_1502))
in (_126_1504, _126_1503)))
in (FStar_ToSMT_Term.mkImp _126_1505))
in (((typing_pred)::(typing_pred_b)::[])::[], (xx)::(aa)::(bb)::[], _126_1506))
in (mkForall_fuel' 2 _126_1507))
in (_126_1508, Some ("ref typing is injective")))
in FStar_ToSMT_Term.Assume (_126_1509))
in (_126_1510)::[])
in (_126_1512)::_126_1511))))))))))
in (
# 1327 "FStar.ToSMT.Encode.fst"
let mk_false_interp = (fun _47_2153 false_tm -> (
# 1328 "FStar.ToSMT.Encode.fst"
let valid = (FStar_ToSMT_Term.mkApp ("Valid", (false_tm)::[]))
in (let _126_1519 = (let _126_1518 = (let _126_1517 = (FStar_ToSMT_Term.mkIff (FStar_ToSMT_Term.mkFalse, valid))
in (_126_1517, Some ("False interpretation")))
in FStar_ToSMT_Term.Assume (_126_1518))
in (_126_1519)::[])))
in (
# 1330 "FStar.ToSMT.Encode.fst"
let mk_and_interp = (fun conj _47_2159 -> (
# 1331 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (
# 1332 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (
# 1333 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1334 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1335 "FStar.ToSMT.Encode.fst"
let valid = (let _126_1526 = (let _126_1525 = (let _126_1524 = (FStar_ToSMT_Term.mkApp (conj, (a)::(b)::[]))
in (_126_1524)::[])
in ("Valid", _126_1525))
in (FStar_ToSMT_Term.mkApp _126_1526))
in (
# 1336 "FStar.ToSMT.Encode.fst"
let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (
# 1337 "FStar.ToSMT.Encode.fst"
let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _126_1533 = (let _126_1532 = (let _126_1531 = (let _126_1530 = (let _126_1529 = (let _126_1528 = (let _126_1527 = (FStar_ToSMT_Term.mkAnd (valid_a, valid_b))
in (_126_1527, valid))
in (FStar_ToSMT_Term.mkIff _126_1528))
in (((valid)::[])::[], (aa)::(bb)::[], _126_1529))
in (FStar_ToSMT_Term.mkForall _126_1530))
in (_126_1531, Some ("/\\ interpretation")))
in FStar_ToSMT_Term.Assume (_126_1532))
in (_126_1533)::[])))))))))
in (
# 1339 "FStar.ToSMT.Encode.fst"
let mk_or_interp = (fun disj _47_2170 -> (
# 1340 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (
# 1341 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (
# 1342 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1343 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1344 "FStar.ToSMT.Encode.fst"
let valid = (let _126_1540 = (let _126_1539 = (let _126_1538 = (FStar_ToSMT_Term.mkApp (disj, (a)::(b)::[]))
in (_126_1538)::[])
in ("Valid", _126_1539))
in (FStar_ToSMT_Term.mkApp _126_1540))
in (
# 1345 "FStar.ToSMT.Encode.fst"
let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (
# 1346 "FStar.ToSMT.Encode.fst"
let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _126_1547 = (let _126_1546 = (let _126_1545 = (let _126_1544 = (let _126_1543 = (let _126_1542 = (let _126_1541 = (FStar_ToSMT_Term.mkOr (valid_a, valid_b))
in (_126_1541, valid))
in (FStar_ToSMT_Term.mkIff _126_1542))
in (((valid)::[])::[], (aa)::(bb)::[], _126_1543))
in (FStar_ToSMT_Term.mkForall _126_1544))
in (_126_1545, Some ("\\/ interpretation")))
in FStar_ToSMT_Term.Assume (_126_1546))
in (_126_1547)::[])))))))))
in (
# 1348 "FStar.ToSMT.Encode.fst"
let mk_eq2_interp = (fun eq2 tt -> (
# 1349 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (
# 1350 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (
# 1351 "FStar.ToSMT.Encode.fst"
let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (
# 1352 "FStar.ToSMT.Encode.fst"
let yy = ("y", FStar_ToSMT_Term.Term_sort)
in (
# 1353 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1354 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1355 "FStar.ToSMT.Encode.fst"
let x = (FStar_ToSMT_Term.mkFreeV xx)
in (
# 1356 "FStar.ToSMT.Encode.fst"
let y = (FStar_ToSMT_Term.mkFreeV yy)
in (
# 1357 "FStar.ToSMT.Encode.fst"
let valid = (let _126_1554 = (let _126_1553 = (let _126_1552 = (FStar_ToSMT_Term.mkApp (eq2, (a)::(b)::(x)::(y)::[]))
in (_126_1552)::[])
in ("Valid", _126_1553))
in (FStar_ToSMT_Term.mkApp _126_1554))
in (let _126_1561 = (let _126_1560 = (let _126_1559 = (let _126_1558 = (let _126_1557 = (let _126_1556 = (let _126_1555 = (FStar_ToSMT_Term.mkEq (x, y))
in (_126_1555, valid))
in (FStar_ToSMT_Term.mkIff _126_1556))
in (((valid)::[])::[], (aa)::(bb)::(xx)::(yy)::[], _126_1557))
in (FStar_ToSMT_Term.mkForall _126_1558))
in (_126_1559, Some ("Eq2 interpretation")))
in FStar_ToSMT_Term.Assume (_126_1560))
in (_126_1561)::[])))))))))))
in (
# 1359 "FStar.ToSMT.Encode.fst"
let mk_imp_interp = (fun imp tt -> (
# 1360 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (
# 1361 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (
# 1362 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1363 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1364 "FStar.ToSMT.Encode.fst"
let valid = (let _126_1568 = (let _126_1567 = (let _126_1566 = (FStar_ToSMT_Term.mkApp (imp, (a)::(b)::[]))
in (_126_1566)::[])
in ("Valid", _126_1567))
in (FStar_ToSMT_Term.mkApp _126_1568))
in (
# 1365 "FStar.ToSMT.Encode.fst"
let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (
# 1366 "FStar.ToSMT.Encode.fst"
let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _126_1575 = (let _126_1574 = (let _126_1573 = (let _126_1572 = (let _126_1571 = (let _126_1570 = (let _126_1569 = (FStar_ToSMT_Term.mkImp (valid_a, valid_b))
in (_126_1569, valid))
in (FStar_ToSMT_Term.mkIff _126_1570))
in (((valid)::[])::[], (aa)::(bb)::[], _126_1571))
in (FStar_ToSMT_Term.mkForall _126_1572))
in (_126_1573, Some ("==> interpretation")))
in FStar_ToSMT_Term.Assume (_126_1574))
in (_126_1575)::[])))))))))
in (
# 1368 "FStar.ToSMT.Encode.fst"
let mk_iff_interp = (fun iff tt -> (
# 1369 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (
# 1370 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (
# 1371 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1372 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1373 "FStar.ToSMT.Encode.fst"
let valid = (let _126_1582 = (let _126_1581 = (let _126_1580 = (FStar_ToSMT_Term.mkApp (iff, (a)::(b)::[]))
in (_126_1580)::[])
in ("Valid", _126_1581))
in (FStar_ToSMT_Term.mkApp _126_1582))
in (
# 1374 "FStar.ToSMT.Encode.fst"
let valid_a = (FStar_ToSMT_Term.mkApp ("Valid", (a)::[]))
in (
# 1375 "FStar.ToSMT.Encode.fst"
let valid_b = (FStar_ToSMT_Term.mkApp ("Valid", (b)::[]))
in (let _126_1589 = (let _126_1588 = (let _126_1587 = (let _126_1586 = (let _126_1585 = (let _126_1584 = (let _126_1583 = (FStar_ToSMT_Term.mkIff (valid_a, valid_b))
in (_126_1583, valid))
in (FStar_ToSMT_Term.mkIff _126_1584))
in (((valid)::[])::[], (aa)::(bb)::[], _126_1585))
in (FStar_ToSMT_Term.mkForall _126_1586))
in (_126_1587, Some ("<==> interpretation")))
in FStar_ToSMT_Term.Assume (_126_1588))
in (_126_1589)::[])))))))))
in (
# 1377 "FStar.ToSMT.Encode.fst"
let mk_forall_interp = (fun for_all tt -> (
# 1378 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (
# 1379 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (
# 1380 "FStar.ToSMT.Encode.fst"
let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (
# 1381 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1382 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1383 "FStar.ToSMT.Encode.fst"
let x = (FStar_ToSMT_Term.mkFreeV xx)
in (
# 1384 "FStar.ToSMT.Encode.fst"
let valid = (let _126_1596 = (let _126_1595 = (let _126_1594 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_126_1594)::[])
in ("Valid", _126_1595))
in (FStar_ToSMT_Term.mkApp _126_1596))
in (
# 1385 "FStar.ToSMT.Encode.fst"
let valid_b_x = (let _126_1599 = (let _126_1598 = (let _126_1597 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_126_1597)::[])
in ("Valid", _126_1598))
in (FStar_ToSMT_Term.mkApp _126_1599))
in (let _126_1613 = (let _126_1612 = (let _126_1611 = (let _126_1610 = (let _126_1609 = (let _126_1608 = (let _126_1607 = (let _126_1606 = (let _126_1605 = (let _126_1601 = (let _126_1600 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_126_1600)::[])
in (_126_1601)::[])
in (let _126_1604 = (let _126_1603 = (let _126_1602 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_126_1602, valid_b_x))
in (FStar_ToSMT_Term.mkImp _126_1603))
in (_126_1605, (xx)::[], _126_1604)))
in (FStar_ToSMT_Term.mkForall _126_1606))
in (_126_1607, valid))
in (FStar_ToSMT_Term.mkIff _126_1608))
in (((valid)::[])::[], (aa)::(bb)::[], _126_1609))
in (FStar_ToSMT_Term.mkForall _126_1610))
in (_126_1611, Some ("forall interpretation")))
in FStar_ToSMT_Term.Assume (_126_1612))
in (_126_1613)::[]))))))))))
in (
# 1387 "FStar.ToSMT.Encode.fst"
let mk_exists_interp = (fun for_all tt -> (
# 1388 "FStar.ToSMT.Encode.fst"
let aa = ("a", FStar_ToSMT_Term.Type_sort)
in (
# 1389 "FStar.ToSMT.Encode.fst"
let bb = ("b", FStar_ToSMT_Term.Type_sort)
in (
# 1390 "FStar.ToSMT.Encode.fst"
let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (
# 1391 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1392 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1393 "FStar.ToSMT.Encode.fst"
let x = (FStar_ToSMT_Term.mkFreeV xx)
in (
# 1394 "FStar.ToSMT.Encode.fst"
let valid = (let _126_1620 = (let _126_1619 = (let _126_1618 = (FStar_ToSMT_Term.mkApp (for_all, (a)::(b)::[]))
in (_126_1618)::[])
in ("Valid", _126_1619))
in (FStar_ToSMT_Term.mkApp _126_1620))
in (
# 1395 "FStar.ToSMT.Encode.fst"
let valid_b_x = (let _126_1623 = (let _126_1622 = (let _126_1621 = (FStar_ToSMT_Term.mk_ApplyTE b x)
in (_126_1621)::[])
in ("Valid", _126_1622))
in (FStar_ToSMT_Term.mkApp _126_1623))
in (let _126_1637 = (let _126_1636 = (let _126_1635 = (let _126_1634 = (let _126_1633 = (let _126_1632 = (let _126_1631 = (let _126_1630 = (let _126_1629 = (let _126_1625 = (let _126_1624 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_126_1624)::[])
in (_126_1625)::[])
in (let _126_1628 = (let _126_1627 = (let _126_1626 = (FStar_ToSMT_Term.mk_HasTypeZ x a)
in (_126_1626, valid_b_x))
in (FStar_ToSMT_Term.mkImp _126_1627))
in (_126_1629, (xx)::[], _126_1628)))
in (FStar_ToSMT_Term.mkExists _126_1630))
in (_126_1631, valid))
in (FStar_ToSMT_Term.mkIff _126_1632))
in (((valid)::[])::[], (aa)::(bb)::[], _126_1633))
in (FStar_ToSMT_Term.mkForall _126_1634))
in (_126_1635, Some ("exists interpretation")))
in FStar_ToSMT_Term.Assume (_126_1636))
in (_126_1637)::[]))))))))))
in (
# 1397 "FStar.ToSMT.Encode.fst"
let mk_foralltyp_interp = (fun for_all tt -> (
# 1398 "FStar.ToSMT.Encode.fst"
let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (
# 1399 "FStar.ToSMT.Encode.fst"
let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (
# 1400 "FStar.ToSMT.Encode.fst"
let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (
# 1401 "FStar.ToSMT.Encode.fst"
let k = (FStar_ToSMT_Term.mkFreeV kk)
in (
# 1402 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1403 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1404 "FStar.ToSMT.Encode.fst"
let valid = (let _126_1644 = (let _126_1643 = (let _126_1642 = (FStar_ToSMT_Term.mkApp (for_all, (k)::(a)::[]))
in (_126_1642)::[])
in ("Valid", _126_1643))
in (FStar_ToSMT_Term.mkApp _126_1644))
in (
# 1405 "FStar.ToSMT.Encode.fst"
let valid_a_b = (let _126_1647 = (let _126_1646 = (let _126_1645 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_126_1645)::[])
in ("Valid", _126_1646))
in (FStar_ToSMT_Term.mkApp _126_1647))
in (let _126_1661 = (let _126_1660 = (let _126_1659 = (let _126_1658 = (let _126_1657 = (let _126_1656 = (let _126_1655 = (let _126_1654 = (let _126_1653 = (let _126_1649 = (let _126_1648 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_126_1648)::[])
in (_126_1649)::[])
in (let _126_1652 = (let _126_1651 = (let _126_1650 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_126_1650, valid_a_b))
in (FStar_ToSMT_Term.mkImp _126_1651))
in (_126_1653, (bb)::[], _126_1652)))
in (FStar_ToSMT_Term.mkForall _126_1654))
in (_126_1655, valid))
in (FStar_ToSMT_Term.mkIff _126_1656))
in (((valid)::[])::[], (kk)::(aa)::[], _126_1657))
in (FStar_ToSMT_Term.mkForall _126_1658))
in (_126_1659, Some ("ForallTyp interpretation")))
in FStar_ToSMT_Term.Assume (_126_1660))
in (_126_1661)::[]))))))))))
in (
# 1407 "FStar.ToSMT.Encode.fst"
let mk_existstyp_interp = (fun for_some tt -> (
# 1408 "FStar.ToSMT.Encode.fst"
let kk = ("k", FStar_ToSMT_Term.Kind_sort)
in (
# 1409 "FStar.ToSMT.Encode.fst"
let aa = ("aa", FStar_ToSMT_Term.Type_sort)
in (
# 1410 "FStar.ToSMT.Encode.fst"
let bb = ("bb", FStar_ToSMT_Term.Term_sort)
in (
# 1411 "FStar.ToSMT.Encode.fst"
let k = (FStar_ToSMT_Term.mkFreeV kk)
in (
# 1412 "FStar.ToSMT.Encode.fst"
let a = (FStar_ToSMT_Term.mkFreeV aa)
in (
# 1413 "FStar.ToSMT.Encode.fst"
let b = (FStar_ToSMT_Term.mkFreeV bb)
in (
# 1414 "FStar.ToSMT.Encode.fst"
let valid = (let _126_1668 = (let _126_1667 = (let _126_1666 = (FStar_ToSMT_Term.mkApp (for_some, (k)::(a)::[]))
in (_126_1666)::[])
in ("Valid", _126_1667))
in (FStar_ToSMT_Term.mkApp _126_1668))
in (
# 1415 "FStar.ToSMT.Encode.fst"
let valid_a_b = (let _126_1671 = (let _126_1670 = (let _126_1669 = (FStar_ToSMT_Term.mk_ApplyTE a b)
in (_126_1669)::[])
in ("Valid", _126_1670))
in (FStar_ToSMT_Term.mkApp _126_1671))
in (let _126_1685 = (let _126_1684 = (let _126_1683 = (let _126_1682 = (let _126_1681 = (let _126_1680 = (let _126_1679 = (let _126_1678 = (let _126_1677 = (let _126_1673 = (let _126_1672 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_126_1672)::[])
in (_126_1673)::[])
in (let _126_1676 = (let _126_1675 = (let _126_1674 = (FStar_ToSMT_Term.mk_HasKind b k)
in (_126_1674, valid_a_b))
in (FStar_ToSMT_Term.mkImp _126_1675))
in (_126_1677, (bb)::[], _126_1676)))
in (FStar_ToSMT_Term.mkExists _126_1678))
in (_126_1679, valid))
in (FStar_ToSMT_Term.mkIff _126_1680))
in (((valid)::[])::[], (kk)::(aa)::[], _126_1681))
in (FStar_ToSMT_Term.mkForall _126_1682))
in (_126_1683, Some ("ExistsTyp interpretation")))
in FStar_ToSMT_Term.Assume (_126_1684))
in (_126_1685)::[]))))))))))
in (
# 1418 "FStar.ToSMT.Encode.fst"
let prims = ((FStar_Absyn_Const.unit_lid, mk_unit))::((FStar_Absyn_Const.bool_lid, mk_bool))::((FStar_Absyn_Const.int_lid, mk_int))::((FStar_Absyn_Const.string_lid, mk_str))::((FStar_Absyn_Const.ref_lid, mk_ref))::((FStar_Absyn_Const.char_lid, mk_int_alias))::((FStar_Absyn_Const.uint8_lid, mk_int_alias))::((FStar_Absyn_Const.false_lid, mk_false_interp))::((FStar_Absyn_Const.and_lid, mk_and_interp))::((FStar_Absyn_Const.or_lid, mk_or_interp))::((FStar_Absyn_Const.eq2_lid, mk_eq2_interp))::((FStar_Absyn_Const.imp_lid, mk_imp_interp))::((FStar_Absyn_Const.iff_lid, mk_iff_interp))::((FStar_Absyn_Const.forall_lid, mk_forall_interp))::((FStar_Absyn_Const.exists_lid, mk_exists_interp))::[]
in (fun t s tt -> (match ((FStar_Util.find_opt (fun _47_2263 -> (match (_47_2263) with
| (l, _47_2262) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some (_47_2266, f) -> begin
(f s tt)
end)))))))))))))))))))))))

# 1441 "FStar.ToSMT.Encode.fst"
let rec encode_sigelt : env_t  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_ToSMT_Term.decls_t * env_t) = (fun env se -> (
# 1442 "FStar.ToSMT.Encode.fst"
let _47_2272 = if (FStar_Tc_Env.debug env.tcenv FStar_Options.Low) then begin
(let _126_1828 = (FStar_Absyn_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") _126_1828))
end else begin
()
end
in (
# 1445 "FStar.ToSMT.Encode.fst"
let nm = (match ((FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (
# 1448 "FStar.ToSMT.Encode.fst"
let _47_2280 = (encode_sigelt' env se)
in (match (_47_2280) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(let _126_1831 = (let _126_1830 = (let _126_1829 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_ToSMT_Term.Caption (_126_1829))
in (_126_1830)::[])
in (_126_1831, e))
end
| _47_2283 -> begin
(let _126_1838 = (let _126_1837 = (let _126_1833 = (let _126_1832 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_126_1832))
in (_126_1833)::g)
in (let _126_1836 = (let _126_1835 = (let _126_1834 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_ToSMT_Term.Caption (_126_1834))
in (_126_1835)::[])
in (FStar_List.append _126_1837 _126_1836)))
in (_126_1838, e))
end)
end)))))
and encode_sigelt' : env_t  ->  FStar_Absyn_Syntax.sigelt  ->  (FStar_ToSMT_Term.decls_t * env_t) = (fun env se -> (
# 1454 "FStar.ToSMT.Encode.fst"
let should_skip = (fun l -> ((((FStar_Util.starts_with l.FStar_Ident.str "Prims.pure_") || (FStar_Util.starts_with l.FStar_Ident.str "Prims.ex_")) || (FStar_Util.starts_with l.FStar_Ident.str "Prims.st_")) || (FStar_Util.starts_with l.FStar_Ident.str "Prims.all_")))
in (
# 1461 "FStar.ToSMT.Encode.fst"
let encode_top_level_val = (fun env lid t quals -> (
# 1462 "FStar.ToSMT.Encode.fst"
let tt = (whnf env t)
in (
# 1463 "FStar.ToSMT.Encode.fst"
let _47_2296 = (encode_free_var env lid t tt quals)
in (match (_47_2296) with
| (decls, env) -> begin
if (FStar_Absyn_Util.is_smt_lemma t) then begin
(let _126_1852 = (let _126_1851 = (encode_smt_lemma env lid t)
in (FStar_List.append decls _126_1851))
in (_126_1852, env))
end else begin
(decls, env)
end
end))))
in (
# 1469 "FStar.ToSMT.Encode.fst"
let encode_top_level_vals = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _47_2303 lb -> (match (_47_2303) with
| (decls, env) -> begin
(
# 1471 "FStar.ToSMT.Encode.fst"
let _47_2307 = (let _126_1861 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (encode_top_level_val env _126_1861 lb.FStar_Absyn_Syntax.lbtyp quals))
in (match (_47_2307) with
| (decls', env) -> begin
((FStar_List.append decls decls'), env)
end))
end)) ([], env))))
in (match (se) with
| FStar_Absyn_Syntax.Sig_typ_abbrev (_47_2309, _47_2311, _47_2313, _47_2315, FStar_Absyn_Syntax.Effect::[], _47_2319) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _47_2324, _47_2326, _47_2328, _47_2330, _47_2332) when (should_skip lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, _47_2337, _47_2339, _47_2341, _47_2343, _47_2345) when (FStar_Ident.lid_equals lid FStar_Absyn_Const.b2t_lid) -> begin
(
# 1480 "FStar.ToSMT.Encode.fst"
let _47_2351 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_47_2351) with
| (tname, ttok, env) -> begin
(
# 1481 "FStar.ToSMT.Encode.fst"
let xx = ("x", FStar_ToSMT_Term.Term_sort)
in (
# 1482 "FStar.ToSMT.Encode.fst"
let x = (FStar_ToSMT_Term.mkFreeV xx)
in (
# 1483 "FStar.ToSMT.Encode.fst"
let valid_b2t_x = (let _126_1864 = (let _126_1863 = (let _126_1862 = (FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[]))
in (_126_1862)::[])
in ("Valid", _126_1863))
in (FStar_ToSMT_Term.mkApp _126_1864))
in (
# 1484 "FStar.ToSMT.Encode.fst"
let decls = (let _126_1872 = (let _126_1871 = (let _126_1870 = (let _126_1869 = (let _126_1868 = (let _126_1867 = (let _126_1866 = (let _126_1865 = (FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[]))
in (valid_b2t_x, _126_1865))
in (FStar_ToSMT_Term.mkEq _126_1866))
in (((valid_b2t_x)::[])::[], (xx)::[], _126_1867))
in (FStar_ToSMT_Term.mkForall _126_1868))
in (_126_1869, Some ("b2t def")))
in FStar_ToSMT_Term.Assume (_126_1870))
in (_126_1871)::[])
in (FStar_ToSMT_Term.DeclFun ((tname, (FStar_ToSMT_Term.Term_sort)::[], FStar_ToSMT_Term.Type_sort, None)))::_126_1872)
in (decls, env)))))
end))
end
| FStar_Absyn_Syntax.Sig_typ_abbrev (lid, tps, _47_2359, t, tags, _47_2363) -> begin
(
# 1491 "FStar.ToSMT.Encode.fst"
let _47_2369 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_47_2369) with
| (tname, ttok, env) -> begin
(
# 1492 "FStar.ToSMT.Encode.fst"
let _47_2378 = (match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_lam (tps', body) -> begin
((FStar_List.append tps tps'), body)
end
| _47_2375 -> begin
(tps, t)
end)
in (match (_47_2378) with
| (tps, t) -> begin
(
# 1495 "FStar.ToSMT.Encode.fst"
let _47_2385 = (encode_binders None tps env)
in (match (_47_2385) with
| (vars, guards, env', binder_decls, _47_2384) -> begin
(
# 1496 "FStar.ToSMT.Encode.fst"
let tok_app = (let _126_1873 = (FStar_ToSMT_Term.mkApp (ttok, []))
in (mk_ApplyT _126_1873 vars))
in (
# 1497 "FStar.ToSMT.Encode.fst"
let tok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, None))
in (
# 1498 "FStar.ToSMT.Encode.fst"
let app = (let _126_1875 = (let _126_1874 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _126_1874))
in (FStar_ToSMT_Term.mkApp _126_1875))
in (
# 1499 "FStar.ToSMT.Encode.fst"
let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _47_2391 -> begin
(let _126_1877 = (let _126_1876 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _126_1876))
in (_126_1877)::[])
end)
in (
# 1502 "FStar.ToSMT.Encode.fst"
let decls = (let _126_1888 = (let _126_1881 = (let _126_1880 = (let _126_1879 = (let _126_1878 = (FStar_List.map Prims.snd vars)
in (tname, _126_1878, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_126_1879))
in (_126_1880)::(tok_decl)::[])
in (FStar_List.append _126_1881 fresh_tok))
in (let _126_1887 = (let _126_1886 = (let _126_1885 = (let _126_1884 = (let _126_1883 = (let _126_1882 = (FStar_ToSMT_Term.mkEq (tok_app, app))
in (((tok_app)::[])::[], vars, _126_1882))
in (FStar_ToSMT_Term.mkForall _126_1883))
in (_126_1884, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_126_1885))
in (_126_1886)::[])
in (FStar_List.append _126_1888 _126_1887)))
in (
# 1506 "FStar.ToSMT.Encode.fst"
let t = if (FStar_All.pipe_right tags (FStar_List.contains FStar_Absyn_Syntax.Opaque)) then begin
(FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
end else begin
(whnf env t)
end
in (
# 1509 "FStar.ToSMT.Encode.fst"
let _47_2403 = if (FStar_All.pipe_right tags (FStar_Util.for_some (fun _47_18 -> (match (_47_18) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _47_2398 -> begin
false
end)))) then begin
(let _126_1891 = (FStar_ToSMT_Term.mk_Valid app)
in (let _126_1890 = (encode_formula t env')
in (_126_1891, _126_1890)))
end else begin
(let _126_1892 = (encode_typ_term t env')
in (app, _126_1892))
end
in (match (_47_2403) with
| (def, (body, decls1)) -> begin
(
# 1513 "FStar.ToSMT.Encode.fst"
let abbrev_def = (let _126_1899 = (let _126_1898 = (let _126_1897 = (let _126_1896 = (let _126_1895 = (let _126_1894 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _126_1893 = (FStar_ToSMT_Term.mkEq (def, body))
in (_126_1894, _126_1893)))
in (FStar_ToSMT_Term.mkImp _126_1895))
in (((def)::[])::[], vars, _126_1896))
in (FStar_ToSMT_Term.mkForall _126_1897))
in (_126_1898, Some ("abbrev. elimination")))
in FStar_ToSMT_Term.Assume (_126_1899))
in (
# 1514 "FStar.ToSMT.Encode.fst"
let kindingAx = (
# 1515 "FStar.ToSMT.Encode.fst"
let _47_2407 = (let _126_1900 = (FStar_Tc_Recheck.recompute_kind t)
in (encode_knd _126_1900 env' app))
in (match (_47_2407) with
| (k, decls) -> begin
(let _126_1908 = (let _126_1907 = (let _126_1906 = (let _126_1905 = (let _126_1904 = (let _126_1903 = (let _126_1902 = (let _126_1901 = (FStar_ToSMT_Term.mk_and_l guards)
in (_126_1901, k))
in (FStar_ToSMT_Term.mkImp _126_1902))
in (((app)::[])::[], vars, _126_1903))
in (FStar_ToSMT_Term.mkForall _126_1904))
in (_126_1905, Some ("abbrev. kinding")))
in FStar_ToSMT_Term.Assume (_126_1906))
in (_126_1907)::[])
in (FStar_List.append decls _126_1908))
end))
in (
# 1517 "FStar.ToSMT.Encode.fst"
let g = (let _126_1909 = (primitive_type_axioms lid tname app)
in (FStar_List.append (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx)) _126_1909))
in (g, env))))
end))))))))
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_val_decl (lid, t, quals, _47_2414) -> begin
if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || env.tcenv.FStar_Tc_Env.is_iface) then begin
(encode_top_level_val env lid t quals)
end else begin
([], env)
end
end
| FStar_Absyn_Syntax.Sig_assume (l, f, _47_2420, _47_2422) -> begin
(
# 1527 "FStar.ToSMT.Encode.fst"
let _47_2427 = (encode_formula f env)
in (match (_47_2427) with
| (f, decls) -> begin
(
# 1528 "FStar.ToSMT.Encode.fst"
let g = (let _126_1914 = (let _126_1913 = (let _126_1912 = (let _126_1911 = (let _126_1910 = (FStar_Absyn_Print.sli l)
in (FStar_Util.format1 "Assumption: %s" _126_1910))
in Some (_126_1911))
in (f, _126_1912))
in FStar_ToSMT_Term.Assume (_126_1913))
in (_126_1914)::[])
in ((FStar_List.append decls g), env))
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _47_2433, datas, quals, _47_2437) when (FStar_Ident.lid_equals t FStar_Absyn_Const.precedes_lid) -> begin
(
# 1532 "FStar.ToSMT.Encode.fst"
let _47_2443 = (new_typ_constant_and_tok_from_lid env t)
in (match (_47_2443) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| FStar_Absyn_Syntax.Sig_tycon (t, _47_2446, _47_2448, _47_2450, _47_2452, _47_2454, _47_2456) when ((FStar_Ident.lid_equals t FStar_Absyn_Const.char_lid) || (FStar_Ident.lid_equals t FStar_Absyn_Const.uint8_lid)) -> begin
(
# 1536 "FStar.ToSMT.Encode.fst"
let tname = t.FStar_Ident.str
in (
# 1537 "FStar.ToSMT.Encode.fst"
let tsym = (FStar_ToSMT_Term.mkFreeV (tname, FStar_ToSMT_Term.Type_sort))
in (
# 1538 "FStar.ToSMT.Encode.fst"
let decl = FStar_ToSMT_Term.DeclFun ((tname, [], FStar_ToSMT_Term.Type_sort, None))
in (let _126_1916 = (let _126_1915 = (primitive_type_axioms t tname tsym)
in (decl)::_126_1915)
in (_126_1916, (push_free_tvar env t tname (Some (tsym))))))))
end
| FStar_Absyn_Syntax.Sig_tycon (t, tps, k, _47_2466, datas, quals, _47_2470) -> begin
(
# 1542 "FStar.ToSMT.Encode.fst"
let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun _47_19 -> (match (_47_19) with
| (FStar_Absyn_Syntax.Logic) | (FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _47_2477 -> begin
false
end))))
in (
# 1543 "FStar.ToSMT.Encode.fst"
let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(
# 1545 "FStar.ToSMT.Encode.fst"
let _47_2487 = c
in (match (_47_2487) with
| (name, args, _47_2484, _47_2486) -> begin
(let _126_1922 = (let _126_1921 = (let _126_1920 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in (name, _126_1920, FStar_ToSMT_Term.Type_sort, None))
in FStar_ToSMT_Term.DeclFun (_126_1921))
in (_126_1922)::[])
end))
end else begin
(FStar_ToSMT_Term.constructor_to_decl c)
end)
in (
# 1549 "FStar.ToSMT.Encode.fst"
let inversion_axioms = (fun tapp vars -> if (((FStar_List.length datas) = 0) || (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (let _126_1928 = (FStar_Tc_Env.lookup_qname env.tcenv l)
in (FStar_All.pipe_right _126_1928 FStar_Option.isNone)))))) then begin
[]
end else begin
(
# 1553 "FStar.ToSMT.Encode.fst"
let _47_2494 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_47_2494) with
| (xxsym, xx) -> begin
(
# 1554 "FStar.ToSMT.Encode.fst"
let _47_2537 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun _47_2497 l -> (match (_47_2497) with
| (out, decls) -> begin
(
# 1555 "FStar.ToSMT.Encode.fst"
let data_t = (FStar_Tc_Env.lookup_datacon env.tcenv l)
in (
# 1556 "FStar.ToSMT.Encode.fst"
let _47_2507 = (match ((FStar_Absyn_Util.function_formals data_t)) with
| Some (formals, res) -> begin
(formals, (FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_47_2507) with
| (args, res) -> begin
(
# 1559 "FStar.ToSMT.Encode.fst"
let indices = (match ((let _126_1931 = (FStar_Absyn_Util.compress_typ res)
in _126_1931.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_app (_47_2509, indices) -> begin
indices
end
| _47_2514 -> begin
[]
end)
in (
# 1562 "FStar.ToSMT.Encode.fst"
let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env a -> (match ((Prims.fst a)) with
| FStar_Util.Inl (a) -> begin
(let _126_1936 = (let _126_1935 = (let _126_1934 = (mk_typ_projector_name l a.FStar_Absyn_Syntax.v)
in (_126_1934, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _126_1935))
in (push_typ_var env a.FStar_Absyn_Syntax.v _126_1936))
end
| FStar_Util.Inr (x) -> begin
(let _126_1939 = (let _126_1938 = (let _126_1937 = (mk_term_projector_name l x.FStar_Absyn_Syntax.v)
in (_126_1937, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _126_1938))
in (push_term_var env x.FStar_Absyn_Syntax.v _126_1939))
end)) env))
in (
# 1565 "FStar.ToSMT.Encode.fst"
let _47_2525 = (encode_args indices env)
in (match (_47_2525) with
| (indices, decls') -> begin
(
# 1566 "FStar.ToSMT.Encode.fst"
let _47_2526 = if ((FStar_List.length indices) <> (FStar_List.length vars)) then begin
(FStar_All.failwith "Impossible")
end else begin
()
end
in (
# 1568 "FStar.ToSMT.Encode.fst"
let eqs = (let _126_1946 = (FStar_List.map2 (fun v a -> (match (a) with
| FStar_Util.Inl (a) -> begin
(let _126_1943 = (let _126_1942 = (FStar_ToSMT_Term.mkFreeV v)
in (_126_1942, a))
in (FStar_ToSMT_Term.mkEq _126_1943))
end
| FStar_Util.Inr (a) -> begin
(let _126_1945 = (let _126_1944 = (FStar_ToSMT_Term.mkFreeV v)
in (_126_1944, a))
in (FStar_ToSMT_Term.mkEq _126_1945))
end)) vars indices)
in (FStar_All.pipe_right _126_1946 FStar_ToSMT_Term.mk_and_l))
in (let _126_1951 = (let _126_1950 = (let _126_1949 = (let _126_1948 = (let _126_1947 = (mk_data_tester env l xx)
in (_126_1947, eqs))
in (FStar_ToSMT_Term.mkAnd _126_1948))
in (out, _126_1949))
in (FStar_ToSMT_Term.mkOr _126_1950))
in (_126_1951, (FStar_List.append decls decls')))))
end))))
end)))
end)) (FStar_ToSMT_Term.mkFalse, [])))
in (match (_47_2537) with
| (data_ax, decls) -> begin
(
# 1572 "FStar.ToSMT.Encode.fst"
let _47_2540 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_47_2540) with
| (ffsym, ff) -> begin
(
# 1573 "FStar.ToSMT.Encode.fst"
let xx_has_type = (let _126_1952 = (FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[]))
in (FStar_ToSMT_Term.mk_HasTypeFuel _126_1952 xx tapp))
in (let _126_1959 = (let _126_1958 = (let _126_1957 = (let _126_1956 = (let _126_1955 = (let _126_1954 = (add_fuel (ffsym, FStar_ToSMT_Term.Fuel_sort) (((xxsym, FStar_ToSMT_Term.Term_sort))::vars))
in (let _126_1953 = (FStar_ToSMT_Term.mkImp (xx_has_type, data_ax))
in (((xx_has_type)::[])::[], _126_1954, _126_1953)))
in (FStar_ToSMT_Term.mkForall _126_1955))
in (_126_1956, Some ("inversion axiom")))
in FStar_ToSMT_Term.Assume (_126_1957))
in (_126_1958)::[])
in (FStar_List.append decls _126_1959)))
end))
end))
end))
end)
in (
# 1577 "FStar.ToSMT.Encode.fst"
let k = (FStar_Absyn_Util.close_kind tps k)
in (
# 1578 "FStar.ToSMT.Encode.fst"
let _47_2552 = (match ((let _126_1960 = (FStar_Absyn_Util.compress_kind k)
in _126_1960.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Kind_arrow (bs, res) -> begin
(true, bs, res)
end
| _47_2548 -> begin
(false, [], k)
end)
in (match (_47_2552) with
| (is_kind_arrow, formals, res) -> begin
(
# 1581 "FStar.ToSMT.Encode.fst"
let _47_2559 = (encode_binders None formals env)
in (match (_47_2559) with
| (vars, guards, env', binder_decls, _47_2558) -> begin
(
# 1583 "FStar.ToSMT.Encode.fst"
let projection_axioms = (fun tapp vars -> (match ((FStar_All.pipe_right quals (FStar_Util.find_opt (fun _47_20 -> (match (_47_20) with
| FStar_Absyn_Syntax.Projector (_47_2565) -> begin
true
end
| _47_2568 -> begin
false
end))))) with
| Some (FStar_Absyn_Syntax.Projector (d, FStar_Util.Inl (a))) -> begin
(
# 1586 "FStar.ToSMT.Encode.fst"
let rec projectee = (fun i _47_21 -> (match (_47_21) with
| [] -> begin
i
end
| f::tl -> begin
(match ((Prims.fst f)) with
| FStar_Util.Inl (_47_2583) -> begin
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
# 1594 "FStar.ToSMT.Encode.fst"
let projectee_pos = (projectee 0 formals)
in (
# 1595 "FStar.ToSMT.Encode.fst"
let _47_2598 = (match ((FStar_Util.first_N projectee_pos vars)) with
| (_47_2589, xx::suffix) -> begin
(xx, suffix)
end
| _47_2595 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_47_2598) with
| (xx, suffix) -> begin
(
# 1598 "FStar.ToSMT.Encode.fst"
let dproj_app = (let _126_1974 = (let _126_1973 = (let _126_1972 = (mk_typ_projector_name d a)
in (let _126_1971 = (let _126_1970 = (FStar_ToSMT_Term.mkFreeV xx)
in (_126_1970)::[])
in (_126_1972, _126_1971)))
in (FStar_ToSMT_Term.mkApp _126_1973))
in (mk_ApplyT _126_1974 suffix))
in (let _126_1979 = (let _126_1978 = (let _126_1977 = (let _126_1976 = (let _126_1975 = (FStar_ToSMT_Term.mkEq (tapp, dproj_app))
in (((tapp)::[])::[], vars, _126_1975))
in (FStar_ToSMT_Term.mkForall _126_1976))
in (_126_1977, Some ("projector axiom")))
in FStar_ToSMT_Term.Assume (_126_1978))
in (_126_1979)::[]))
end))))
end
| _47_2601 -> begin
[]
end))
in (
# 1602 "FStar.ToSMT.Encode.fst"
let pretype_axioms = (fun tapp vars -> (
# 1603 "FStar.ToSMT.Encode.fst"
let _47_2607 = (fresh_fvar "x" FStar_ToSMT_Term.Term_sort)
in (match (_47_2607) with
| (xxsym, xx) -> begin
(
# 1604 "FStar.ToSMT.Encode.fst"
let _47_2610 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_47_2610) with
| (ffsym, ff) -> begin
(
# 1605 "FStar.ToSMT.Encode.fst"
let xx_has_type = (FStar_ToSMT_Term.mk_HasTypeFuel ff xx tapp)
in (let _126_1992 = (let _126_1991 = (let _126_1990 = (let _126_1989 = (let _126_1988 = (let _126_1987 = (let _126_1986 = (let _126_1985 = (let _126_1984 = (FStar_ToSMT_Term.mkApp ("PreType", (xx)::[]))
in (tapp, _126_1984))
in (FStar_ToSMT_Term.mkEq _126_1985))
in (xx_has_type, _126_1986))
in (FStar_ToSMT_Term.mkImp _126_1987))
in (((xx_has_type)::[])::[], ((xxsym, FStar_ToSMT_Term.Term_sort))::((ffsym, FStar_ToSMT_Term.Fuel_sort))::vars, _126_1988))
in (FStar_ToSMT_Term.mkForall _126_1989))
in (_126_1990, Some ("pretyping")))
in FStar_ToSMT_Term.Assume (_126_1991))
in (_126_1992)::[]))
end))
end)))
in (
# 1609 "FStar.ToSMT.Encode.fst"
let _47_2615 = (new_typ_constant_and_tok_from_lid env t)
in (match (_47_2615) with
| (tname, ttok, env) -> begin
(
# 1610 "FStar.ToSMT.Encode.fst"
let ttok_tm = (FStar_ToSMT_Term.mkApp (ttok, []))
in (
# 1611 "FStar.ToSMT.Encode.fst"
let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (
# 1612 "FStar.ToSMT.Encode.fst"
let tapp = (let _126_1994 = (let _126_1993 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (tname, _126_1993))
in (FStar_ToSMT_Term.mkApp _126_1994))
in (
# 1613 "FStar.ToSMT.Encode.fst"
let _47_2636 = (
# 1614 "FStar.ToSMT.Encode.fst"
let tname_decl = (let _126_1998 = (let _126_1997 = (FStar_All.pipe_right vars (FStar_List.map (fun _47_2621 -> (match (_47_2621) with
| (n, s) -> begin
((Prims.strcat tname n), s)
end))))
in (let _126_1996 = (varops.next_id ())
in (tname, _126_1997, FStar_ToSMT_Term.Type_sort, _126_1996)))
in (constructor_or_logic_type_decl _126_1998))
in (
# 1615 "FStar.ToSMT.Encode.fst"
let _47_2633 = (match (vars) with
| [] -> begin
(let _126_2002 = (let _126_2001 = (let _126_2000 = (FStar_ToSMT_Term.mkApp (tname, []))
in (FStar_All.pipe_left (fun _126_1999 -> Some (_126_1999)) _126_2000))
in (push_free_tvar env t tname _126_2001))
in ([], _126_2002))
end
| _47_2625 -> begin
(
# 1618 "FStar.ToSMT.Encode.fst"
let ttok_decl = FStar_ToSMT_Term.DeclFun ((ttok, [], FStar_ToSMT_Term.Type_sort, Some ("token")))
in (
# 1619 "FStar.ToSMT.Encode.fst"
let ttok_fresh = (let _126_2003 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ttok, FStar_ToSMT_Term.Type_sort) _126_2003))
in (
# 1620 "FStar.ToSMT.Encode.fst"
let ttok_app = (mk_ApplyT ttok_tm vars)
in (
# 1621 "FStar.ToSMT.Encode.fst"
let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (
# 1628 "FStar.ToSMT.Encode.fst"
let name_tok_corr = (let _126_2007 = (let _126_2006 = (let _126_2005 = (let _126_2004 = (FStar_ToSMT_Term.mkEq (ttok_app, tapp))
in (pats, None, vars, _126_2004))
in (FStar_ToSMT_Term.mkForall' _126_2005))
in (_126_2006, Some ("name-token correspondence")))
in FStar_ToSMT_Term.Assume (_126_2007))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_47_2633) with
| (tok_decls, env) -> begin
((FStar_List.append tname_decl tok_decls), env)
end)))
in (match (_47_2636) with
| (decls, env) -> begin
(
# 1631 "FStar.ToSMT.Encode.fst"
let kindingAx = (
# 1632 "FStar.ToSMT.Encode.fst"
let _47_2639 = (encode_knd res env' tapp)
in (match (_47_2639) with
| (k, decls) -> begin
(
# 1633 "FStar.ToSMT.Encode.fst"
let karr = if is_kind_arrow then begin
(let _126_2011 = (let _126_2010 = (let _126_2009 = (let _126_2008 = (FStar_ToSMT_Term.mk_PreKind ttok_tm)
in (FStar_ToSMT_Term.mk_tester "Kind_arrow" _126_2008))
in (_126_2009, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_126_2010))
in (_126_2011)::[])
end else begin
[]
end
in (let _126_2017 = (let _126_2016 = (let _126_2015 = (let _126_2014 = (let _126_2013 = (let _126_2012 = (FStar_ToSMT_Term.mkImp (guard, k))
in (((tapp)::[])::[], vars, _126_2012))
in (FStar_ToSMT_Term.mkForall _126_2013))
in (_126_2014, Some ("kinding")))
in FStar_ToSMT_Term.Assume (_126_2015))
in (_126_2016)::[])
in (FStar_List.append (FStar_List.append decls karr) _126_2017)))
end))
in (
# 1638 "FStar.ToSMT.Encode.fst"
let aux = if is_logical then begin
(let _126_2018 = (projection_axioms tapp vars)
in (FStar_List.append kindingAx _126_2018))
end else begin
(let _126_2025 = (let _126_2023 = (let _126_2021 = (let _126_2019 = (primitive_type_axioms t tname tapp)
in (FStar_List.append kindingAx _126_2019))
in (let _126_2020 = (inversion_axioms tapp vars)
in (FStar_List.append _126_2021 _126_2020)))
in (let _126_2022 = (projection_axioms tapp vars)
in (FStar_List.append _126_2023 _126_2022)))
in (let _126_2024 = (pretype_axioms tapp vars)
in (FStar_List.append _126_2025 _126_2024)))
end
in (
# 1647 "FStar.ToSMT.Encode.fst"
let g = (FStar_List.append (FStar_List.append decls binder_decls) aux)
in (g, env))))
end)))))
end))))
end))
end))))))
end
| FStar_Absyn_Syntax.Sig_datacon (d, _47_2646, _47_2648, _47_2650, _47_2652, _47_2654) when (FStar_Ident.lid_equals d FStar_Absyn_Const.lexcons_lid) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_datacon (d, t, (_47_2660, tps, _47_2663), quals, _47_2667, drange) -> begin
(
# 1655 "FStar.ToSMT.Encode.fst"
let t = (let _126_2027 = (FStar_List.map (fun _47_2674 -> (match (_47_2674) with
| (x, _47_2673) -> begin
(x, Some (FStar_Absyn_Syntax.Implicit (true)))
end)) tps)
in (FStar_Absyn_Util.close_typ _126_2027 t))
in (
# 1656 "FStar.ToSMT.Encode.fst"
let _47_2679 = (new_term_constant_and_tok_from_lid env d)
in (match (_47_2679) with
| (ddconstrsym, ddtok, env) -> begin
(
# 1657 "FStar.ToSMT.Encode.fst"
let ddtok_tm = (FStar_ToSMT_Term.mkApp (ddtok, []))
in (
# 1658 "FStar.ToSMT.Encode.fst"
let _47_2688 = (match ((FStar_Absyn_Util.function_formals t)) with
| Some (f, c) -> begin
(f, (FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_47_2688) with
| (formals, t_res) -> begin
(
# 1661 "FStar.ToSMT.Encode.fst"
let _47_2691 = (fresh_fvar "f" FStar_ToSMT_Term.Fuel_sort)
in (match (_47_2691) with
| (fuel_var, fuel_tm) -> begin
(
# 1662 "FStar.ToSMT.Encode.fst"
let s_fuel_tm = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (
# 1663 "FStar.ToSMT.Encode.fst"
let _47_2698 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_47_2698) with
| (vars, guards, env', binder_decls, names) -> begin
(
# 1664 "FStar.ToSMT.Encode.fst"
let projectors = (FStar_All.pipe_right names (FStar_List.map (fun _47_22 -> (match (_47_22) with
| FStar_Util.Inl (a) -> begin
(let _126_2029 = (mk_typ_projector_name d a)
in (_126_2029, FStar_ToSMT_Term.Type_sort))
end
| FStar_Util.Inr (x) -> begin
(let _126_2030 = (mk_term_projector_name d x)
in (_126_2030, FStar_ToSMT_Term.Term_sort))
end))))
in (
# 1667 "FStar.ToSMT.Encode.fst"
let datacons = (let _126_2032 = (let _126_2031 = (varops.next_id ())
in (ddconstrsym, projectors, FStar_ToSMT_Term.Term_sort, _126_2031))
in (FStar_All.pipe_right _126_2032 FStar_ToSMT_Term.constructor_to_decl))
in (
# 1668 "FStar.ToSMT.Encode.fst"
let app = (mk_ApplyE ddtok_tm vars)
in (
# 1669 "FStar.ToSMT.Encode.fst"
let guard = (FStar_ToSMT_Term.mk_and_l guards)
in (
# 1670 "FStar.ToSMT.Encode.fst"
let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (
# 1671 "FStar.ToSMT.Encode.fst"
let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (
# 1673 "FStar.ToSMT.Encode.fst"
let _47_2712 = (encode_typ_pred None t env ddtok_tm)
in (match (_47_2712) with
| (tok_typing, decls3) -> begin
(
# 1675 "FStar.ToSMT.Encode.fst"
let _47_2719 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_47_2719) with
| (vars', guards', env'', decls_formals, _47_2718) -> begin
(
# 1676 "FStar.ToSMT.Encode.fst"
let _47_2724 = (
# 1677 "FStar.ToSMT.Encode.fst"
let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars')
in (
# 1678 "FStar.ToSMT.Encode.fst"
let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (_47_2724) with
| (ty_pred', decls_pred) -> begin
(
# 1680 "FStar.ToSMT.Encode.fst"
let guard' = (FStar_ToSMT_Term.mk_and_l guards')
in (
# 1681 "FStar.ToSMT.Encode.fst"
let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _47_2728 -> begin
(let _126_2034 = (let _126_2033 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (ddtok, FStar_ToSMT_Term.Term_sort) _126_2033))
in (_126_2034)::[])
end)
in (
# 1685 "FStar.ToSMT.Encode.fst"
let encode_elim = (fun _47_2731 -> (match (()) with
| () -> begin
(
# 1686 "FStar.ToSMT.Encode.fst"
let _47_2734 = (FStar_Absyn_Util.head_and_args t_res)
in (match (_47_2734) with
| (head, args) -> begin
(match ((let _126_2037 = (FStar_Absyn_Util.compress_typ head)
in _126_2037.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Typ_const (fv) -> begin
(
# 1689 "FStar.ToSMT.Encode.fst"
let encoded_head = (lookup_free_tvar_name env' fv)
in (
# 1690 "FStar.ToSMT.Encode.fst"
let _47_2740 = (encode_args args env')
in (match (_47_2740) with
| (encoded_args, arg_decls) -> begin
(
# 1691 "FStar.ToSMT.Encode.fst"
let _47_2764 = (FStar_List.fold_left (fun _47_2744 arg -> (match (_47_2744) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| FStar_Util.Inl (targ) -> begin
(
# 1694 "FStar.ToSMT.Encode.fst"
let _47_2752 = (let _126_2040 = (FStar_Absyn_Util.new_bvd None)
in (gen_typ_var env _126_2040))
in (match (_47_2752) with
| (_47_2749, tv, env) -> begin
(let _126_2042 = (let _126_2041 = (FStar_ToSMT_Term.mkEq (targ, tv))
in (_126_2041)::eqns)
in (env, (tv)::arg_vars, _126_2042))
end))
end
| FStar_Util.Inr (varg) -> begin
(
# 1697 "FStar.ToSMT.Encode.fst"
let _47_2759 = (let _126_2043 = (FStar_Absyn_Util.new_bvd None)
in (gen_term_var env _126_2043))
in (match (_47_2759) with
| (_47_2756, xv, env) -> begin
(let _126_2045 = (let _126_2044 = (FStar_ToSMT_Term.mkEq (varg, xv))
in (_126_2044)::eqns)
in (env, (xv)::arg_vars, _126_2045))
end))
end)
end)) (env', [], []) encoded_args)
in (match (_47_2764) with
| (_47_2761, arg_vars, eqns) -> begin
(
# 1699 "FStar.ToSMT.Encode.fst"
let arg_vars = (FStar_List.rev arg_vars)
in (
# 1700 "FStar.ToSMT.Encode.fst"
let ty = (FStar_ToSMT_Term.mkApp (encoded_head, arg_vars))
in (
# 1701 "FStar.ToSMT.Encode.fst"
let xvars = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (
# 1702 "FStar.ToSMT.Encode.fst"
let dapp = (FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (
# 1703 "FStar.ToSMT.Encode.fst"
let ty_pred = (FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (
# 1704 "FStar.ToSMT.Encode.fst"
let arg_binders = (FStar_List.map FStar_ToSMT_Term.fv_of_term arg_vars)
in (
# 1705 "FStar.ToSMT.Encode.fst"
let typing_inversion = (let _126_2052 = (let _126_2051 = (let _126_2050 = (let _126_2049 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _126_2048 = (let _126_2047 = (let _126_2046 = (FStar_ToSMT_Term.mk_and_l (FStar_List.append eqns guards))
in (ty_pred, _126_2046))
in (FStar_ToSMT_Term.mkImp _126_2047))
in (((ty_pred)::[])::[], _126_2049, _126_2048)))
in (FStar_ToSMT_Term.mkForall _126_2050))
in (_126_2051, Some ("data constructor typing elim")))
in FStar_ToSMT_Term.Assume (_126_2052))
in (
# 1710 "FStar.ToSMT.Encode.fst"
let subterm_ordering = if (FStar_Ident.lid_equals d FStar_Absyn_Const.lextop_lid) then begin
(
# 1712 "FStar.ToSMT.Encode.fst"
let x = (let _126_2053 = (varops.fresh "x")
in (_126_2053, FStar_ToSMT_Term.Term_sort))
in (
# 1713 "FStar.ToSMT.Encode.fst"
let xtm = (FStar_ToSMT_Term.mkFreeV x)
in (let _126_2063 = (let _126_2062 = (let _126_2061 = (let _126_2060 = (let _126_2055 = (let _126_2054 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_126_2054)::[])
in (_126_2055)::[])
in (let _126_2059 = (let _126_2058 = (let _126_2057 = (FStar_ToSMT_Term.mk_tester "LexCons" xtm)
in (let _126_2056 = (FStar_ToSMT_Term.mk_Precedes xtm dapp)
in (_126_2057, _126_2056)))
in (FStar_ToSMT_Term.mkImp _126_2058))
in (_126_2060, (x)::[], _126_2059)))
in (FStar_ToSMT_Term.mkForall _126_2061))
in (_126_2062, Some ("lextop is top")))
in FStar_ToSMT_Term.Assume (_126_2063))))
end else begin
(
# 1716 "FStar.ToSMT.Encode.fst"
let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| (FStar_ToSMT_Term.Type_sort) | (FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| FStar_ToSMT_Term.Term_sort -> begin
(let _126_2066 = (let _126_2065 = (FStar_ToSMT_Term.mkFreeV v)
in (FStar_ToSMT_Term.mk_Precedes _126_2065 dapp))
in (_126_2066)::[])
end
| _47_2779 -> begin
(FStar_All.failwith "unexpected sort")
end))))
in (let _126_2073 = (let _126_2072 = (let _126_2071 = (let _126_2070 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) (FStar_List.append vars arg_binders))
in (let _126_2069 = (let _126_2068 = (let _126_2067 = (FStar_ToSMT_Term.mk_and_l prec)
in (ty_pred, _126_2067))
in (FStar_ToSMT_Term.mkImp _126_2068))
in (((ty_pred)::[])::[], _126_2070, _126_2069)))
in (FStar_ToSMT_Term.mkForall _126_2071))
in (_126_2072, Some ("subterm ordering")))
in FStar_ToSMT_Term.Assume (_126_2073)))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _47_2783 -> begin
(
# 1725 "FStar.ToSMT.Encode.fst"
let _47_2784 = (let _126_2076 = (let _126_2075 = (FStar_Absyn_Print.sli d)
in (let _126_2074 = (FStar_Absyn_Print.typ_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" _126_2075 _126_2074)))
in (FStar_Tc_Errors.warn drange _126_2076))
in ([], []))
end)
end))
end))
in (
# 1727 "FStar.ToSMT.Encode.fst"
let _47_2788 = (encode_elim ())
in (match (_47_2788) with
| (decls2, elim) -> begin
(
# 1728 "FStar.ToSMT.Encode.fst"
let g = (let _126_2101 = (let _126_2100 = (let _126_2085 = (let _126_2084 = (let _126_2083 = (let _126_2082 = (let _126_2081 = (let _126_2080 = (let _126_2079 = (let _126_2078 = (let _126_2077 = (FStar_Absyn_Print.sli d)
in (FStar_Util.format1 "data constructor proxy: %s" _126_2077))
in Some (_126_2078))
in (ddtok, [], FStar_ToSMT_Term.Term_sort, _126_2079))
in FStar_ToSMT_Term.DeclFun (_126_2080))
in (_126_2081)::[])
in (FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) decls3) _126_2082))
in (FStar_List.append _126_2083 proxy_fresh))
in (FStar_List.append _126_2084 decls_formals))
in (FStar_List.append _126_2085 decls_pred))
in (let _126_2099 = (let _126_2098 = (let _126_2097 = (let _126_2089 = (let _126_2088 = (let _126_2087 = (let _126_2086 = (FStar_ToSMT_Term.mkEq (app, dapp))
in (((app)::[])::[], vars, _126_2086))
in (FStar_ToSMT_Term.mkForall _126_2087))
in (_126_2088, Some ("equality for proxy")))
in FStar_ToSMT_Term.Assume (_126_2089))
in (let _126_2096 = (let _126_2095 = (let _126_2094 = (let _126_2093 = (let _126_2092 = (let _126_2091 = (add_fuel (fuel_var, FStar_ToSMT_Term.Fuel_sort) vars')
in (let _126_2090 = (FStar_ToSMT_Term.mkImp (guard', ty_pred'))
in (((ty_pred')::[])::[], _126_2091, _126_2090)))
in (FStar_ToSMT_Term.mkForall _126_2092))
in (_126_2093, Some ("data constructor typing intro")))
in FStar_ToSMT_Term.Assume (_126_2094))
in (_126_2095)::[])
in (_126_2097)::_126_2096))
in (FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::_126_2098)
in (FStar_List.append _126_2100 _126_2099)))
in (FStar_List.append _126_2101 elim))
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
| FStar_Absyn_Syntax.Sig_bundle (ses, _47_2792, _47_2794, _47_2796) -> begin
(
# 1744 "FStar.ToSMT.Encode.fst"
let _47_2801 = (encode_signature env ses)
in (match (_47_2801) with
| (g, env) -> begin
(
# 1745 "FStar.ToSMT.Encode.fst"
let _47_2813 = (FStar_All.pipe_right g (FStar_List.partition (fun _47_23 -> (match (_47_23) with
| FStar_ToSMT_Term.Assume (_47_2804, Some ("inversion axiom")) -> begin
false
end
| _47_2810 -> begin
true
end))))
in (match (_47_2813) with
| (g', inversions) -> begin
(
# 1748 "FStar.ToSMT.Encode.fst"
let _47_2822 = (FStar_All.pipe_right g' (FStar_List.partition (fun _47_24 -> (match (_47_24) with
| FStar_ToSMT_Term.DeclFun (_47_2816) -> begin
true
end
| _47_2819 -> begin
false
end))))
in (match (_47_2822) with
| (decls, rest) -> begin
((FStar_List.append (FStar_List.append decls rest) inversions), env)
end))
end))
end))
end
| FStar_Absyn_Syntax.Sig_let (_47_2824, _47_2826, _47_2828, quals) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun _47_25 -> (match (_47_25) with
| (FStar_Absyn_Syntax.Projector (_)) | (FStar_Absyn_Syntax.Discriminator (_)) -> begin
true
end
| _47_2840 -> begin
false
end)))) -> begin
([], env)
end
| FStar_Absyn_Syntax.Sig_let ((is_rec, bindings), _47_2845, _47_2847, quals) -> begin
(
# 1757 "FStar.ToSMT.Encode.fst"
let eta_expand = (fun binders formals body t -> (
# 1758 "FStar.ToSMT.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1759 "FStar.ToSMT.Encode.fst"
let _47_2859 = (FStar_Util.first_N nbinders formals)
in (match (_47_2859) with
| (formals, extra_formals) -> begin
(
# 1760 "FStar.ToSMT.Encode.fst"
let subst = (FStar_List.map2 (fun formal binder -> (match (((Prims.fst formal), (Prims.fst binder))) with
| (FStar_Util.Inl (a), FStar_Util.Inl (b)) -> begin
(let _126_2116 = (let _126_2115 = (FStar_Absyn_Util.btvar_to_typ b)
in (a.FStar_Absyn_Syntax.v, _126_2115))
in FStar_Util.Inl (_126_2116))
end
| (FStar_Util.Inr (x), FStar_Util.Inr (y)) -> begin
(let _126_2118 = (let _126_2117 = (FStar_Absyn_Util.bvar_to_exp y)
in (x.FStar_Absyn_Syntax.v, _126_2117))
in FStar_Util.Inr (_126_2118))
end
| _47_2873 -> begin
(FStar_All.failwith "Impossible")
end)) formals binders)
in (
# 1764 "FStar.ToSMT.Encode.fst"
let extra_formals = (let _126_2119 = (FStar_Absyn_Util.subst_binders subst extra_formals)
in (FStar_All.pipe_right _126_2119 FStar_Absyn_Util.name_binders))
in (
# 1765 "FStar.ToSMT.Encode.fst"
let body = (let _126_2125 = (let _126_2121 = (let _126_2120 = (FStar_Absyn_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd _126_2120))
in (body, _126_2121))
in (let _126_2124 = (let _126_2123 = (FStar_Absyn_Util.subst_typ subst t)
in (FStar_All.pipe_left (fun _126_2122 -> Some (_126_2122)) _126_2123))
in (FStar_Absyn_Syntax.mk_Exp_app_flat _126_2125 _126_2124 body.FStar_Absyn_Syntax.pos)))
in ((FStar_List.append binders extra_formals), body))))
end))))
in (
# 1768 "FStar.ToSMT.Encode.fst"
let destruct_bound_function = (fun flid t_norm e -> (match (e.FStar_Absyn_Syntax.n) with
| (FStar_Absyn_Syntax.Exp_ascribed ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_abs (binders, body); FStar_Absyn_Syntax.tk = _; FStar_Absyn_Syntax.pos = _; FStar_Absyn_Syntax.fvs = _; FStar_Absyn_Syntax.uvs = _}, _, _)) | (FStar_Absyn_Syntax.Exp_abs (binders, body)) -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(
# 1773 "FStar.ToSMT.Encode.fst"
let nformals = (FStar_List.length formals)
in (
# 1774 "FStar.ToSMT.Encode.fst"
let nbinders = (FStar_List.length binders)
in (
# 1775 "FStar.ToSMT.Encode.fst"
let tres = (FStar_Absyn_Util.comp_result c)
in if ((nformals < nbinders) && (FStar_Absyn_Util.is_total_comp c)) then begin
(
# 1777 "FStar.ToSMT.Encode.fst"
let _47_2911 = (FStar_Util.first_N nformals binders)
in (match (_47_2911) with
| (bs0, rest) -> begin
(
# 1778 "FStar.ToSMT.Encode.fst"
let tres = (match ((FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(FStar_Absyn_Util.subst_typ s tres)
end
| _47_2915 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 1781 "FStar.ToSMT.Encode.fst"
let body = (FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (tres)) body.FStar_Absyn_Syntax.pos)
in (bs0, body, bs0, tres)))
end))
end else begin
if (nformals > nbinders) then begin
(
# 1785 "FStar.ToSMT.Encode.fst"
let _47_2920 = (eta_expand binders formals body tres)
in (match (_47_2920) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end
| _47_2922 -> begin
(let _126_2134 = (let _126_2133 = (FStar_Absyn_Print.exp_to_string e)
in (let _126_2132 = (FStar_Absyn_Print.typ_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str _126_2133 _126_2132)))
in (FStar_All.failwith _126_2134))
end)
end
| _47_2924 -> begin
(match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (formals, c) -> begin
(
# 1796 "FStar.ToSMT.Encode.fst"
let tres = (FStar_Absyn_Util.comp_result c)
in (
# 1797 "FStar.ToSMT.Encode.fst"
let _47_2932 = (eta_expand [] formals e tres)
in (match (_47_2932) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _47_2934 -> begin
([], e, [], t_norm)
end)
end))
in (FStar_All.try_with (fun _47_2936 -> (match (()) with
| () -> begin
if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _47_26 -> (match (_47_26) with
| FStar_Absyn_Syntax.Opaque -> begin
true
end
| _47_2947 -> begin
false
end)))) || (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp))))) then begin
(encode_top_level_vals env bindings quals)
end else begin
(
# 1806 "FStar.ToSMT.Encode.fst"
let _47_2966 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun _47_2953 lb -> (match (_47_2953) with
| (toks, typs, decls, env) -> begin
(
# 1808 "FStar.ToSMT.Encode.fst"
let _47_2955 = if (FStar_Absyn_Util.is_smt_lemma lb.FStar_Absyn_Syntax.lbtyp) then begin
(Prims.raise Let_rec_unencodeable)
end else begin
()
end
in (
# 1809 "FStar.ToSMT.Encode.fst"
let t_norm = (let _126_2140 = (whnf env lb.FStar_Absyn_Syntax.lbtyp)
in (FStar_All.pipe_right _126_2140 FStar_Absyn_Util.compress_typ))
in (
# 1810 "FStar.ToSMT.Encode.fst"
let _47_2961 = (let _126_2141 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (declare_top_level_let env _126_2141 lb.FStar_Absyn_Syntax.lbtyp t_norm))
in (match (_47_2961) with
| (tok, decl, env) -> begin
(let _126_2144 = (let _126_2143 = (let _126_2142 = (FStar_Util.right lb.FStar_Absyn_Syntax.lbname)
in (_126_2142, tok))
in (_126_2143)::toks)
in (_126_2144, (t_norm)::typs, (decl)::decls, env))
end))))
end)) ([], [], [], env)))
in (match (_47_2966) with
| (toks, typs, decls, env) -> begin
(
# 1812 "FStar.ToSMT.Encode.fst"
let toks = (FStar_List.rev toks)
in (
# 1813 "FStar.ToSMT.Encode.fst"
let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (
# 1814 "FStar.ToSMT.Encode.fst"
let typs = (FStar_List.rev typs)
in if ((FStar_All.pipe_right quals (FStar_Util.for_some (fun _47_27 -> (match (_47_27) with
| FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _47_2973 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> ((FStar_Absyn_Util.is_lemma t) || (let _126_2147 = (FStar_Absyn_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation _126_2147))))))) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ({FStar_Absyn_Syntax.lbname = _47_2981; FStar_Absyn_Syntax.lbtyp = _47_2979; FStar_Absyn_Syntax.lbeff = _47_2977; FStar_Absyn_Syntax.lbdef = e}::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(
# 1821 "FStar.ToSMT.Encode.fst"
let _47_2997 = (destruct_bound_function flid t_norm e)
in (match (_47_2997) with
| (binders, body, formals, tres) -> begin
(
# 1822 "FStar.ToSMT.Encode.fst"
let _47_3004 = (encode_binders None binders env)
in (match (_47_3004) with
| (vars, guards, env', binder_decls, _47_3003) -> begin
(
# 1823 "FStar.ToSMT.Encode.fst"
let app = (match (vars) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (f, FStar_ToSMT_Term.Term_sort))
end
| _47_3007 -> begin
(let _126_2149 = (let _126_2148 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (f, _126_2148))
in (FStar_ToSMT_Term.mkApp _126_2149))
end)
in (
# 1824 "FStar.ToSMT.Encode.fst"
let _47_3011 = (encode_exp body env')
in (match (_47_3011) with
| (body, decls2) -> begin
(
# 1825 "FStar.ToSMT.Encode.fst"
let eqn = (let _126_2158 = (let _126_2157 = (let _126_2154 = (let _126_2153 = (let _126_2152 = (let _126_2151 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _126_2150 = (FStar_ToSMT_Term.mkEq (app, body))
in (_126_2151, _126_2150)))
in (FStar_ToSMT_Term.mkImp _126_2152))
in (((app)::[])::[], vars, _126_2153))
in (FStar_ToSMT_Term.mkForall _126_2154))
in (let _126_2156 = (let _126_2155 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (_126_2155))
in (_126_2157, _126_2156)))
in FStar_ToSMT_Term.Assume (_126_2158))
in ((FStar_List.append (FStar_List.append (FStar_List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end))
end
| _47_3014 -> begin
(FStar_All.failwith "Impossible")
end)
end else begin
(
# 1828 "FStar.ToSMT.Encode.fst"
let fuel = (let _126_2159 = (varops.fresh "fuel")
in (_126_2159, FStar_ToSMT_Term.Fuel_sort))
in (
# 1829 "FStar.ToSMT.Encode.fst"
let fuel_tm = (FStar_ToSMT_Term.mkFreeV fuel)
in (
# 1830 "FStar.ToSMT.Encode.fst"
let env0 = env
in (
# 1831 "FStar.ToSMT.Encode.fst"
let _47_3031 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun _47_3020 _47_3025 -> (match ((_47_3020, _47_3025)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(
# 1832 "FStar.ToSMT.Encode.fst"
let g = (varops.new_fvar flid)
in (
# 1833 "FStar.ToSMT.Encode.fst"
let gtok = (varops.new_fvar flid)
in (
# 1834 "FStar.ToSMT.Encode.fst"
let env = (let _126_2164 = (let _126_2163 = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))
in (FStar_All.pipe_left (fun _126_2162 -> Some (_126_2162)) _126_2163))
in (push_free_var env flid gtok _126_2164))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)))
in (match (_47_3031) with
| (gtoks, env) -> begin
(
# 1836 "FStar.ToSMT.Encode.fst"
let gtoks = (FStar_List.rev gtoks)
in (
# 1837 "FStar.ToSMT.Encode.fst"
let encode_one_binding = (fun env0 _47_3040 t_norm _47_3049 -> (match ((_47_3040, _47_3049)) with
| ((flid, f, ftok, g, gtok), {FStar_Absyn_Syntax.lbname = _47_3048; FStar_Absyn_Syntax.lbtyp = _47_3046; FStar_Absyn_Syntax.lbeff = _47_3044; FStar_Absyn_Syntax.lbdef = e}) -> begin
(
# 1838 "FStar.ToSMT.Encode.fst"
let _47_3054 = (destruct_bound_function flid t_norm e)
in (match (_47_3054) with
| (binders, body, formals, tres) -> begin
(
# 1839 "FStar.ToSMT.Encode.fst"
let _47_3061 = (encode_binders None binders env)
in (match (_47_3061) with
| (vars, guards, env', binder_decls, _47_3060) -> begin
(
# 1840 "FStar.ToSMT.Encode.fst"
let decl_g = (let _126_2175 = (let _126_2174 = (let _126_2173 = (FStar_List.map Prims.snd vars)
in (FStar_ToSMT_Term.Fuel_sort)::_126_2173)
in (g, _126_2174, FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in FStar_ToSMT_Term.DeclFun (_126_2175))
in (
# 1841 "FStar.ToSMT.Encode.fst"
let env0 = (push_zfuel_name env0 flid g)
in (
# 1842 "FStar.ToSMT.Encode.fst"
let decl_g_tok = FStar_ToSMT_Term.DeclFun ((gtok, [], FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (
# 1843 "FStar.ToSMT.Encode.fst"
let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (
# 1844 "FStar.ToSMT.Encode.fst"
let app = (FStar_ToSMT_Term.mkApp (f, vars_tm))
in (
# 1845 "FStar.ToSMT.Encode.fst"
let gsapp = (let _126_2178 = (let _126_2177 = (let _126_2176 = (FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (_126_2176)::vars_tm)
in (g, _126_2177))
in (FStar_ToSMT_Term.mkApp _126_2178))
in (
# 1846 "FStar.ToSMT.Encode.fst"
let gmax = (let _126_2181 = (let _126_2180 = (let _126_2179 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (_126_2179)::vars_tm)
in (g, _126_2180))
in (FStar_ToSMT_Term.mkApp _126_2181))
in (
# 1847 "FStar.ToSMT.Encode.fst"
let _47_3071 = (encode_exp body env')
in (match (_47_3071) with
| (body_tm, decls2) -> begin
(
# 1848 "FStar.ToSMT.Encode.fst"
let eqn_g = (let _126_2190 = (let _126_2189 = (let _126_2186 = (let _126_2185 = (let _126_2184 = (let _126_2183 = (FStar_ToSMT_Term.mk_and_l guards)
in (let _126_2182 = (FStar_ToSMT_Term.mkEq (gsapp, body_tm))
in (_126_2183, _126_2182)))
in (FStar_ToSMT_Term.mkImp _126_2184))
in (((gsapp)::[])::[], (fuel)::vars, _126_2185))
in (FStar_ToSMT_Term.mkForall _126_2186))
in (let _126_2188 = (let _126_2187 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (_126_2187))
in (_126_2189, _126_2188)))
in FStar_ToSMT_Term.Assume (_126_2190))
in (
# 1849 "FStar.ToSMT.Encode.fst"
let eqn_f = (let _126_2194 = (let _126_2193 = (let _126_2192 = (let _126_2191 = (FStar_ToSMT_Term.mkEq (app, gmax))
in (((app)::[])::[], vars, _126_2191))
in (FStar_ToSMT_Term.mkForall _126_2192))
in (_126_2193, Some ("Correspondence of recursive function to instrumented version")))
in FStar_ToSMT_Term.Assume (_126_2194))
in (
# 1850 "FStar.ToSMT.Encode.fst"
let eqn_g' = (let _126_2203 = (let _126_2202 = (let _126_2201 = (let _126_2200 = (let _126_2199 = (let _126_2198 = (let _126_2197 = (let _126_2196 = (let _126_2195 = (FStar_ToSMT_Term.n_fuel 0)
in (_126_2195)::vars_tm)
in (g, _126_2196))
in (FStar_ToSMT_Term.mkApp _126_2197))
in (gsapp, _126_2198))
in (FStar_ToSMT_Term.mkEq _126_2199))
in (((gsapp)::[])::[], (fuel)::vars, _126_2200))
in (FStar_ToSMT_Term.mkForall _126_2201))
in (_126_2202, Some ("Fuel irrelevance")))
in FStar_ToSMT_Term.Assume (_126_2203))
in (
# 1851 "FStar.ToSMT.Encode.fst"
let _47_3094 = (
# 1852 "FStar.ToSMT.Encode.fst"
let _47_3081 = (encode_binders None formals env0)
in (match (_47_3081) with
| (vars, v_guards, env, binder_decls, _47_3080) -> begin
(
# 1853 "FStar.ToSMT.Encode.fst"
let vars_tm = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (
# 1854 "FStar.ToSMT.Encode.fst"
let gapp = (FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (
# 1855 "FStar.ToSMT.Encode.fst"
let tok_corr = (
# 1856 "FStar.ToSMT.Encode.fst"
let tok_app = (let _126_2204 = (FStar_ToSMT_Term.mkFreeV (gtok, FStar_ToSMT_Term.Term_sort))
in (mk_ApplyE _126_2204 ((fuel)::vars)))
in (let _126_2208 = (let _126_2207 = (let _126_2206 = (let _126_2205 = (FStar_ToSMT_Term.mkEq (tok_app, gapp))
in (((tok_app)::[])::[], (fuel)::vars, _126_2205))
in (FStar_ToSMT_Term.mkForall _126_2206))
in (_126_2207, Some ("Fuel token correspondence")))
in FStar_ToSMT_Term.Assume (_126_2208)))
in (
# 1858 "FStar.ToSMT.Encode.fst"
let _47_3091 = (
# 1859 "FStar.ToSMT.Encode.fst"
let _47_3088 = (encode_typ_pred None tres env gapp)
in (match (_47_3088) with
| (g_typing, d3) -> begin
(let _126_2216 = (let _126_2215 = (let _126_2214 = (let _126_2213 = (let _126_2212 = (let _126_2211 = (let _126_2210 = (let _126_2209 = (FStar_ToSMT_Term.mk_and_l v_guards)
in (_126_2209, g_typing))
in (FStar_ToSMT_Term.mkImp _126_2210))
in (((gapp)::[])::[], (fuel)::vars, _126_2211))
in (FStar_ToSMT_Term.mkForall _126_2212))
in (_126_2213, None))
in FStar_ToSMT_Term.Assume (_126_2214))
in (_126_2215)::[])
in (d3, _126_2216))
end))
in (match (_47_3091) with
| (aux_decls, typing_corr) -> begin
((FStar_List.append binder_decls aux_decls), (FStar_List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_47_3094) with
| (aux_decls, g_typing) -> begin
((FStar_List.append (FStar_List.append (FStar_List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (
# 1863 "FStar.ToSMT.Encode.fst"
let _47_3110 = (let _126_2219 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun _47_3098 _47_3102 -> (match ((_47_3098, _47_3102)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(
# 1864 "FStar.ToSMT.Encode.fst"
let _47_3106 = (encode_one_binding env0 gtok ty bs)
in (match (_47_3106) with
| (decls', eqns', env0) -> begin
((decls')::decls, (FStar_List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) _126_2219))
in (match (_47_3110) with
| (decls, eqns, env0) -> begin
(
# 1866 "FStar.ToSMT.Encode.fst"
let _47_3119 = (let _126_2221 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right _126_2221 (FStar_List.partition (fun _47_28 -> (match (_47_28) with
| FStar_ToSMT_Term.DeclFun (_47_3113) -> begin
true
end
| _47_3116 -> begin
false
end)))))
in (match (_47_3119) with
| (prefix_decls, rest) -> begin
(
# 1869 "FStar.ToSMT.Encode.fst"
let eqns = (FStar_List.rev eqns)
in ((FStar_List.append (FStar_List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end
end)))
end))
end
end)) (fun _47_2935 -> (match (_47_2935) with
| Let_rec_unencodeable -> begin
(
# 1872 "FStar.ToSMT.Encode.fst"
let msg = (let _126_2224 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Absyn_Print.lbname_to_string lb.FStar_Absyn_Syntax.lbname))))
in (FStar_All.pipe_right _126_2224 (FStar_String.concat " and ")))
in (
# 1873 "FStar.ToSMT.Encode.fst"
let decl = FStar_ToSMT_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| (FStar_Absyn_Syntax.Sig_pragma (_)) | (FStar_Absyn_Syntax.Sig_main (_)) | (FStar_Absyn_Syntax.Sig_new_effect (_)) | (FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end)))))
and declare_top_level_let : env_t  ->  FStar_Ident.lident  ->  FStar_Absyn_Syntax.typ  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  ((Prims.string * FStar_ToSMT_Term.term Prims.option) * FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (match ((try_lookup_lid env x)) with
| None -> begin
(
# 1887 "FStar.ToSMT.Encode.fst"
let _47_3146 = (encode_free_var env x t t_norm [])
in (match (_47_3146) with
| (decls, env) -> begin
(
# 1888 "FStar.ToSMT.Encode.fst"
let _47_3151 = (lookup_lid env x)
in (match (_47_3151) with
| (n, x', _47_3150) -> begin
((n, x'), decls, env)
end))
end))
end
| Some (n, x, _47_3155) -> begin
((n, x), [], env)
end))
and encode_smt_lemma : env_t  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_ToSMT_Term.decl Prims.list = (fun env lid t -> (
# 1894 "FStar.ToSMT.Encode.fst"
let _47_3163 = (encode_function_type_as_formula None None t env)
in (match (_47_3163) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_ToSMT_Term.Assume ((form, Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str)))))::[]))
end)))
and encode_free_var : env_t  ->  FStar_Ident.lident  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax  ->  FStar_Absyn_Syntax.qualifier Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env lid tt t_norm quals -> if ((let _126_2237 = (FStar_Absyn_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation _126_2237)) || (FStar_Absyn_Util.is_lemma t_norm)) then begin
(
# 1899 "FStar.ToSMT.Encode.fst"
let _47_3172 = (new_term_constant_and_tok_from_lid env lid)
in (match (_47_3172) with
| (vname, vtok, env) -> begin
(
# 1900 "FStar.ToSMT.Encode.fst"
let arg_sorts = (match (t_norm.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_fun (binders, _47_3175) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun _47_29 -> (match (_47_29) with
| (FStar_Util.Inl (_47_3180), _47_3183) -> begin
FStar_ToSMT_Term.Type_sort
end
| _47_3186 -> begin
FStar_ToSMT_Term.Term_sort
end))))
end
| _47_3188 -> begin
[]
end)
in (
# 1903 "FStar.ToSMT.Encode.fst"
let d = FStar_ToSMT_Term.DeclFun ((vname, arg_sorts, FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (
# 1904 "FStar.ToSMT.Encode.fst"
let dd = FStar_ToSMT_Term.DeclFun ((vtok, [], FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(
# 1907 "FStar.ToSMT.Encode.fst"
let vname = (varops.new_fvar lid)
in (
# 1908 "FStar.ToSMT.Encode.fst"
let definition = (prims.mk lid vname)
in (
# 1909 "FStar.ToSMT.Encode.fst"
let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(
# 1911 "FStar.ToSMT.Encode.fst"
let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (
# 1912 "FStar.ToSMT.Encode.fst"
let _47_3205 = (match ((FStar_Absyn_Util.function_formals t_norm)) with
| Some (args, comp) -> begin
if encode_non_total_function_typ then begin
(let _126_2239 = (FStar_Tc_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in (args, _126_2239))
end else begin
(args, (None, (FStar_Absyn_Util.comp_result comp)))
end
end
| None -> begin
([], (None, t_norm))
end)
in (match (_47_3205) with
| (formals, (pre_opt, res_t)) -> begin
(
# 1918 "FStar.ToSMT.Encode.fst"
let _47_3209 = (new_term_constant_and_tok_from_lid env lid)
in (match (_47_3209) with
| (vname, vtok, env) -> begin
(
# 1919 "FStar.ToSMT.Encode.fst"
let vtok_tm = (match (formals) with
| [] -> begin
(FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
end
| _47_3212 -> begin
(FStar_ToSMT_Term.mkApp (vtok, []))
end)
in (
# 1922 "FStar.ToSMT.Encode.fst"
let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun _47_30 -> (match (_47_30) with
| FStar_Absyn_Syntax.Discriminator (d) -> begin
(
# 1924 "FStar.ToSMT.Encode.fst"
let _47_3228 = (FStar_Util.prefix vars)
in (match (_47_3228) with
| (_47_3223, (xxsym, _47_3226)) -> begin
(
# 1925 "FStar.ToSMT.Encode.fst"
let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (let _126_2256 = (let _126_2255 = (let _126_2254 = (let _126_2253 = (let _126_2252 = (let _126_2251 = (let _126_2250 = (let _126_2249 = (FStar_ToSMT_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_ToSMT_Term.boxBool _126_2249))
in (vapp, _126_2250))
in (FStar_ToSMT_Term.mkEq _126_2251))
in (((vapp)::[])::[], vars, _126_2252))
in (FStar_ToSMT_Term.mkForall _126_2253))
in (_126_2254, Some ("Discriminator equation")))
in FStar_ToSMT_Term.Assume (_126_2255))
in (_126_2256)::[]))
end))
end
| FStar_Absyn_Syntax.Projector (d, FStar_Util.Inr (f)) -> begin
(
# 1930 "FStar.ToSMT.Encode.fst"
let _47_3241 = (FStar_Util.prefix vars)
in (match (_47_3241) with
| (_47_3236, (xxsym, _47_3239)) -> begin
(
# 1931 "FStar.ToSMT.Encode.fst"
let xx = (FStar_ToSMT_Term.mkFreeV (xxsym, FStar_ToSMT_Term.Term_sort))
in (
# 1932 "FStar.ToSMT.Encode.fst"
let prim_app = (let _126_2258 = (let _126_2257 = (mk_term_projector_name d f)
in (_126_2257, (xx)::[]))
in (FStar_ToSMT_Term.mkApp _126_2258))
in (let _126_2263 = (let _126_2262 = (let _126_2261 = (let _126_2260 = (let _126_2259 = (FStar_ToSMT_Term.mkEq (vapp, prim_app))
in (((vapp)::[])::[], vars, _126_2259))
in (FStar_ToSMT_Term.mkForall _126_2260))
in (_126_2261, Some ("Projector equation")))
in FStar_ToSMT_Term.Assume (_126_2262))
in (_126_2263)::[])))
end))
end
| _47_3245 -> begin
[]
end)))))
in (
# 1936 "FStar.ToSMT.Encode.fst"
let _47_3252 = (encode_binders None formals env)
in (match (_47_3252) with
| (vars, guards, env', decls1, _47_3251) -> begin
(
# 1937 "FStar.ToSMT.Encode.fst"
let _47_3261 = (match (pre_opt) with
| None -> begin
(let _126_2264 = (FStar_ToSMT_Term.mk_and_l guards)
in (_126_2264, decls1))
end
| Some (p) -> begin
(
# 1939 "FStar.ToSMT.Encode.fst"
let _47_3258 = (encode_formula p env')
in (match (_47_3258) with
| (g, ds) -> begin
(let _126_2265 = (FStar_ToSMT_Term.mk_and_l ((g)::guards))
in (_126_2265, (FStar_List.append decls1 ds)))
end))
end)
in (match (_47_3261) with
| (guard, decls1) -> begin
(
# 1940 "FStar.ToSMT.Encode.fst"
let vtok_app = (mk_ApplyE vtok_tm vars)
in (
# 1942 "FStar.ToSMT.Encode.fst"
let vapp = (let _126_2267 = (let _126_2266 = (FStar_List.map FStar_ToSMT_Term.mkFreeV vars)
in (vname, _126_2266))
in (FStar_ToSMT_Term.mkApp _126_2267))
in (
# 1943 "FStar.ToSMT.Encode.fst"
let _47_3292 = (
# 1944 "FStar.ToSMT.Encode.fst"
let vname_decl = (let _126_2270 = (let _126_2269 = (FStar_All.pipe_right formals (FStar_List.map (fun _47_31 -> (match (_47_31) with
| (FStar_Util.Inl (_47_3266), _47_3269) -> begin
FStar_ToSMT_Term.Type_sort
end
| _47_3272 -> begin
FStar_ToSMT_Term.Term_sort
end))))
in (vname, _126_2269, FStar_ToSMT_Term.Term_sort, None))
in FStar_ToSMT_Term.DeclFun (_126_2270))
in (
# 1945 "FStar.ToSMT.Encode.fst"
let _47_3279 = (
# 1946 "FStar.ToSMT.Encode.fst"
let env = (
# 1946 "FStar.ToSMT.Encode.fst"
let _47_3274 = env
in {bindings = _47_3274.bindings; depth = _47_3274.depth; tcenv = _47_3274.tcenv; warn = _47_3274.warn; cache = _47_3274.cache; nolabels = _47_3274.nolabels; use_zfuel_name = _47_3274.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in if (not ((head_normal env tt))) then begin
(encode_typ_pred None tt env vtok_tm)
end else begin
(encode_typ_pred None t_norm env vtok_tm)
end)
in (match (_47_3279) with
| (tok_typing, decls2) -> begin
(
# 1950 "FStar.ToSMT.Encode.fst"
let tok_typing = FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in (
# 1951 "FStar.ToSMT.Encode.fst"
let _47_3289 = (match (formals) with
| [] -> begin
(let _126_2274 = (let _126_2273 = (let _126_2272 = (FStar_ToSMT_Term.mkFreeV (vname, FStar_ToSMT_Term.Term_sort))
in (FStar_All.pipe_left (fun _126_2271 -> Some (_126_2271)) _126_2272))
in (push_free_var env lid vname _126_2273))
in ((FStar_List.append decls2 ((tok_typing)::[])), _126_2274))
end
| _47_3283 -> begin
(
# 1954 "FStar.ToSMT.Encode.fst"
let vtok_decl = FStar_ToSMT_Term.DeclFun ((vtok, [], FStar_ToSMT_Term.Term_sort, None))
in (
# 1955 "FStar.ToSMT.Encode.fst"
let vtok_fresh = (let _126_2275 = (varops.next_id ())
in (FStar_ToSMT_Term.fresh_token (vtok, FStar_ToSMT_Term.Term_sort) _126_2275))
in (
# 1956 "FStar.ToSMT.Encode.fst"
let name_tok_corr = (let _126_2279 = (let _126_2278 = (let _126_2277 = (let _126_2276 = (FStar_ToSMT_Term.mkEq (vtok_app, vapp))
in (((vtok_app)::[])::[], vars, _126_2276))
in (FStar_ToSMT_Term.mkForall _126_2277))
in (_126_2278, None))
in FStar_ToSMT_Term.Assume (_126_2279))
in ((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))))
end)
in (match (_47_3289) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
end)))
in (match (_47_3292) with
| (decls2, env) -> begin
(
# 1959 "FStar.ToSMT.Encode.fst"
let _47_3300 = (
# 1960 "FStar.ToSMT.Encode.fst"
let res_t = (FStar_Absyn_Util.compress_typ res_t)
in (
# 1961 "FStar.ToSMT.Encode.fst"
let _47_3296 = (encode_typ_term res_t env')
in (match (_47_3296) with
| (encoded_res_t, decls) -> begin
(let _126_2280 = (FStar_ToSMT_Term.mk_HasType vapp encoded_res_t)
in (encoded_res_t, _126_2280, decls))
end)))
in (match (_47_3300) with
| (encoded_res_t, ty_pred, decls3) -> begin
(
# 1963 "FStar.ToSMT.Encode.fst"
let typingAx = (let _126_2284 = (let _126_2283 = (let _126_2282 = (let _126_2281 = (FStar_ToSMT_Term.mkImp (guard, ty_pred))
in (((vapp)::[])::[], vars, _126_2281))
in (FStar_ToSMT_Term.mkForall _126_2282))
in (_126_2283, Some ("free var typing")))
in FStar_ToSMT_Term.Assume (_126_2284))
in (
# 1964 "FStar.ToSMT.Encode.fst"
let g = (let _126_2286 = (let _126_2285 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::_126_2285)
in (FStar_List.append (FStar_List.append (FStar_List.append decls1 decls2) decls3) _126_2286))
in (g, env)))
end))
end))))
end))
end))))
end))
end)))
end
end)
and encode_signature : env_t  ->  FStar_Absyn_Syntax.sigelt Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun _47_3307 se -> (match (_47_3307) with
| (g, env) -> begin
(
# 1970 "FStar.ToSMT.Encode.fst"
let _47_3311 = (encode_sigelt env se)
in (match (_47_3311) with
| (g', env) -> begin
((FStar_List.append g g'), env)
end))
end)) ([], env))))

# 1973 "FStar.ToSMT.Encode.fst"
let encode_env_bindings : env_t  ->  FStar_Tc_Env.binding Prims.list  ->  (FStar_ToSMT_Term.decl Prims.list * env_t) = (fun env bindings -> (
# 1998 "FStar.ToSMT.Encode.fst"
let encode_binding = (fun b _47_3318 -> (match (_47_3318) with
| (decls, env) -> begin
(match (b) with
| FStar_Tc_Env.Binding_var (x, t0) -> begin
(
# 2000 "FStar.ToSMT.Encode.fst"
let _47_3326 = (new_term_constant env x)
in (match (_47_3326) with
| (xxsym, xx, env') -> begin
(
# 2001 "FStar.ToSMT.Encode.fst"
let t1 = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (
# 2002 "FStar.ToSMT.Encode.fst"
let _47_3328 = if (FStar_All.pipe_left (FStar_Tc_Env.debug env.tcenv) (FStar_Options.Other ("Encoding"))) then begin
(let _126_2301 = (FStar_Absyn_Print.strBvd x)
in (let _126_2300 = (FStar_Absyn_Print.typ_to_string t0)
in (let _126_2299 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" _126_2301 _126_2300 _126_2299))))
end else begin
()
end
in (
# 2004 "FStar.ToSMT.Encode.fst"
let _47_3332 = (encode_typ_pred None t1 env xx)
in (match (_47_3332) with
| (t, decls') -> begin
(
# 2005 "FStar.ToSMT.Encode.fst"
let caption = if (FStar_ST.read FStar_Options.logQueries) then begin
(let _126_2305 = (let _126_2304 = (FStar_Absyn_Print.strBvd x)
in (let _126_2303 = (FStar_Absyn_Print.typ_to_string t0)
in (let _126_2302 = (FStar_Absyn_Print.typ_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" _126_2304 _126_2303 _126_2302))))
in Some (_126_2305))
end else begin
None
end
in (
# 2009 "FStar.ToSMT.Encode.fst"
let g = (FStar_List.append (FStar_List.append ((FStar_ToSMT_Term.DeclFun ((xxsym, [], FStar_ToSMT_Term.Term_sort, caption)))::[]) decls') ((FStar_ToSMT_Term.Assume ((t, None)))::[]))
in ((FStar_List.append decls g), env')))
end))))
end))
end
| FStar_Tc_Env.Binding_typ (a, k) -> begin
(
# 2014 "FStar.ToSMT.Encode.fst"
let _47_3342 = (new_typ_constant env a)
in (match (_47_3342) with
| (aasym, aa, env') -> begin
(
# 2015 "FStar.ToSMT.Encode.fst"
let _47_3345 = (encode_knd k env aa)
in (match (_47_3345) with
| (k, decls') -> begin
(
# 2016 "FStar.ToSMT.Encode.fst"
let g = (let _126_2311 = (let _126_2310 = (let _126_2309 = (let _126_2308 = (let _126_2307 = (let _126_2306 = (FStar_Absyn_Print.strBvd a)
in Some (_126_2306))
in (aasym, [], FStar_ToSMT_Term.Type_sort, _126_2307))
in FStar_ToSMT_Term.DeclFun (_126_2308))
in (_126_2309)::[])
in (FStar_List.append _126_2310 decls'))
in (FStar_List.append _126_2311 ((FStar_ToSMT_Term.Assume ((k, None)))::[])))
in ((FStar_List.append decls g), env'))
end))
end))
end
| FStar_Tc_Env.Binding_lid (x, t) -> begin
(
# 2021 "FStar.ToSMT.Encode.fst"
let t_norm = (whnf env t)
in (
# 2022 "FStar.ToSMT.Encode.fst"
let _47_3354 = (encode_free_var env x t t_norm [])
in (match (_47_3354) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end)))
end
| FStar_Tc_Env.Binding_sig (se) -> begin
(
# 2025 "FStar.ToSMT.Encode.fst"
let _47_3359 = (encode_sigelt env se)
in (match (_47_3359) with
| (g, env') -> begin
((FStar_List.append decls g), env')
end))
end)
end))
in (FStar_List.fold_right encode_binding bindings ([], env))))

# 2029 "FStar.ToSMT.Encode.fst"
let encode_labels = (fun labs -> (
# 2030 "FStar.ToSMT.Encode.fst"
let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun _47_3366 -> (match (_47_3366) with
| (l, _47_3363, _47_3365) -> begin
FStar_ToSMT_Term.DeclFun (((Prims.fst l), [], FStar_ToSMT_Term.Bool_sort, None))
end))))
in (
# 2031 "FStar.ToSMT.Encode.fst"
let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun _47_3373 -> (match (_47_3373) with
| (l, _47_3370, _47_3372) -> begin
(let _126_2319 = (FStar_All.pipe_left (fun _126_2315 -> FStar_ToSMT_Term.Echo (_126_2315)) (Prims.fst l))
in (let _126_2318 = (let _126_2317 = (let _126_2316 = (FStar_ToSMT_Term.mkFreeV l)
in FStar_ToSMT_Term.Eval (_126_2316))
in (_126_2317)::[])
in (_126_2319)::_126_2318))
end))))
in (prefix, suffix))))

# 2036 "FStar.ToSMT.Encode.fst"
let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 2037 "FStar.ToSMT.Encode.fst"
let init_env : FStar_Tc_Env.env  ->  Prims.unit = (fun tcenv -> (let _126_2324 = (let _126_2323 = (let _126_2322 = (FStar_Util.smap_create 100)
in {bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = _126_2322; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (_126_2323)::[])
in (FStar_ST.op_Colon_Equals last_env _126_2324)))

# 2040 "FStar.ToSMT.Encode.fst"
let get_env : FStar_Tc_Env.env  ->  env_t = (fun tcenv -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "No env; call init first!")
end
| e::_47_3379 -> begin
(
# 2042 "FStar.ToSMT.Encode.fst"
let _47_3382 = e
in {bindings = _47_3382.bindings; depth = _47_3382.depth; tcenv = tcenv; warn = _47_3382.warn; cache = _47_3382.cache; nolabels = _47_3382.nolabels; use_zfuel_name = _47_3382.use_zfuel_name; encode_non_total_function_typ = _47_3382.encode_non_total_function_typ})
end))

# 2043 "FStar.ToSMT.Encode.fst"
let set_env : env_t  ->  Prims.unit = (fun env -> (match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| _47_3388::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl))
end))

# 2046 "FStar.ToSMT.Encode.fst"
let push_env : Prims.unit  ->  Prims.unit = (fun _47_3390 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Empty env stack")
end
| hd::tl -> begin
(
# 2049 "FStar.ToSMT.Encode.fst"
let refs = (FStar_Util.smap_copy hd.cache)
in (
# 2050 "FStar.ToSMT.Encode.fst"
let top = (
# 2050 "FStar.ToSMT.Encode.fst"
let _47_3396 = hd
in {bindings = _47_3396.bindings; depth = _47_3396.depth; tcenv = _47_3396.tcenv; warn = _47_3396.warn; cache = refs; nolabels = _47_3396.nolabels; use_zfuel_name = _47_3396.use_zfuel_name; encode_non_total_function_typ = _47_3396.encode_non_total_function_typ})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd)::tl))))
end)
end))

# 2052 "FStar.ToSMT.Encode.fst"
let pop_env : Prims.unit  ->  Prims.unit = (fun _47_3399 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| [] -> begin
(FStar_All.failwith "Popping an empty stack")
end
| _47_3403::tl -> begin
(FStar_ST.op_Colon_Equals last_env tl)
end)
end))

# 2055 "FStar.ToSMT.Encode.fst"
let mark_env : Prims.unit  ->  Prims.unit = (fun _47_3405 -> (match (()) with
| () -> begin
(push_env ())
end))

# 2056 "FStar.ToSMT.Encode.fst"
let reset_mark_env : Prims.unit  ->  Prims.unit = (fun _47_3406 -> (match (()) with
| () -> begin
(pop_env ())
end))

# 2057 "FStar.ToSMT.Encode.fst"
let commit_mark_env : Prims.unit  ->  Prims.unit = (fun _47_3407 -> (match (()) with
| () -> begin
(match ((FStar_ST.read last_env)) with
| hd::_47_3410::tl -> begin
(FStar_ST.op_Colon_Equals last_env ((hd)::tl))
end
| _47_3415 -> begin
(FStar_All.failwith "Impossible")
end)
end))

# 2063 "FStar.ToSMT.Encode.fst"
let init : FStar_Tc_Env.env  ->  Prims.unit = (fun tcenv -> (
# 2064 "FStar.ToSMT.Encode.fst"
let _47_3417 = (init_env tcenv)
in (
# 2065 "FStar.ToSMT.Encode.fst"
let _47_3419 = (FStar_ToSMT_Z3.init ())
in (FStar_ToSMT_Z3.giveZ3 ((FStar_ToSMT_Term.DefPrelude)::[])))))

# 2067 "FStar.ToSMT.Encode.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 2068 "FStar.ToSMT.Encode.fst"
let _47_3422 = (push_env ())
in (
# 2069 "FStar.ToSMT.Encode.fst"
let _47_3424 = (varops.push ())
in (FStar_ToSMT_Z3.push msg))))

# 2071 "FStar.ToSMT.Encode.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 2072 "FStar.ToSMT.Encode.fst"
let _47_3427 = (let _126_2345 = (pop_env ())
in (FStar_All.pipe_left Prims.ignore _126_2345))
in (
# 2073 "FStar.ToSMT.Encode.fst"
let _47_3429 = (varops.pop ())
in (FStar_ToSMT_Z3.pop msg))))

# 2075 "FStar.ToSMT.Encode.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 2076 "FStar.ToSMT.Encode.fst"
let _47_3432 = (mark_env ())
in (
# 2077 "FStar.ToSMT.Encode.fst"
let _47_3434 = (varops.mark ())
in (FStar_ToSMT_Z3.mark msg))))

# 2079 "FStar.ToSMT.Encode.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 2080 "FStar.ToSMT.Encode.fst"
let _47_3437 = (reset_mark_env ())
in (
# 2081 "FStar.ToSMT.Encode.fst"
let _47_3439 = (varops.reset_mark ())
in (FStar_ToSMT_Z3.reset_mark msg))))

# 2083 "FStar.ToSMT.Encode.fst"
let commit_mark = (fun msg -> (
# 2084 "FStar.ToSMT.Encode.fst"
let _47_3442 = (commit_mark_env ())
in (
# 2085 "FStar.ToSMT.Encode.fst"
let _47_3444 = (varops.commit_mark ())
in (FStar_ToSMT_Z3.commit_mark msg))))

# 2087 "FStar.ToSMT.Encode.fst"
let encode_sig : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (
# 2088 "FStar.ToSMT.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(let _126_2359 = (let _126_2358 = (let _126_2357 = (FStar_Absyn_Print.sigelt_to_string_short se)
in (Prims.strcat "encoding sigelt " _126_2357))
in FStar_ToSMT_Term.Caption (_126_2358))
in (_126_2359)::decls)
end else begin
decls
end)
in (
# 2092 "FStar.ToSMT.Encode.fst"
let env = (get_env tcenv)
in (
# 2093 "FStar.ToSMT.Encode.fst"
let _47_3453 = (encode_sigelt env se)
in (match (_47_3453) with
| (decls, env) -> begin
(
# 2094 "FStar.ToSMT.Encode.fst"
let _47_3454 = (set_env env)
in (let _126_2360 = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 _126_2360)))
end)))))

# 2097 "FStar.ToSMT.Encode.fst"
let encode_modul : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (
# 2098 "FStar.ToSMT.Encode.fst"
let name = (FStar_Util.format2 "%s %s" (if modul.FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.FStar_Absyn_Syntax.name.FStar_Ident.str)
in (
# 2099 "FStar.ToSMT.Encode.fst"
let _47_3459 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _126_2365 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Absyn_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "Encoding externals for %s ... %s exports\n" name _126_2365))
end else begin
()
end
in (
# 2101 "FStar.ToSMT.Encode.fst"
let env = (get_env tcenv)
in (
# 2102 "FStar.ToSMT.Encode.fst"
let _47_3466 = (encode_signature (
# 2102 "FStar.ToSMT.Encode.fst"
let _47_3462 = env
in {bindings = _47_3462.bindings; depth = _47_3462.depth; tcenv = _47_3462.tcenv; warn = false; cache = _47_3462.cache; nolabels = _47_3462.nolabels; use_zfuel_name = _47_3462.use_zfuel_name; encode_non_total_function_typ = _47_3462.encode_non_total_function_typ}) modul.FStar_Absyn_Syntax.exports)
in (match (_47_3466) with
| (decls, env) -> begin
(
# 2103 "FStar.ToSMT.Encode.fst"
let caption = (fun decls -> if (FStar_ST.read FStar_Options.logQueries) then begin
(
# 2105 "FStar.ToSMT.Encode.fst"
let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::decls) ((FStar_ToSMT_Term.Caption ((Prims.strcat "End " msg)))::[])))
end else begin
decls
end)
in (
# 2108 "FStar.ToSMT.Encode.fst"
let _47_3472 = (set_env (
# 2108 "FStar.ToSMT.Encode.fst"
let _47_3470 = env
in {bindings = _47_3470.bindings; depth = _47_3470.depth; tcenv = _47_3470.tcenv; warn = true; cache = _47_3470.cache; nolabels = _47_3470.nolabels; use_zfuel_name = _47_3470.use_zfuel_name; encode_non_total_function_typ = _47_3470.encode_non_total_function_typ}))
in (
# 2109 "FStar.ToSMT.Encode.fst"
let _47_3474 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end else begin
()
end
in (
# 2110 "FStar.ToSMT.Encode.fst"
let decls = (caption decls)
in (FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

# 2113 "FStar.ToSMT.Encode.fst"
let solve : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.unit = (fun tcenv q -> (
# 2114 "FStar.ToSMT.Encode.fst"
let _47_3479 = (let _126_2374 = (let _126_2373 = (let _126_2372 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _126_2372))
in (FStar_Util.format1 "Starting query at %s" _126_2373))
in (push _126_2374))
in (
# 2115 "FStar.ToSMT.Encode.fst"
let pop = (fun _47_3482 -> (match (()) with
| () -> begin
(let _126_2379 = (let _126_2378 = (let _126_2377 = (FStar_Tc_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _126_2377))
in (FStar_Util.format1 "Ending query at %s" _126_2378))
in (pop _126_2379))
end))
in (
# 2116 "FStar.ToSMT.Encode.fst"
let _47_3541 = (
# 2117 "FStar.ToSMT.Encode.fst"
let env = (get_env tcenv)
in (
# 2118 "FStar.ToSMT.Encode.fst"
let bindings = (FStar_Tc_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (
# 2119 "FStar.ToSMT.Encode.fst"
let _47_3515 = (
# 2120 "FStar.ToSMT.Encode.fst"
let rec aux = (fun bindings -> (match (bindings) with
| FStar_Tc_Env.Binding_var (x, t)::rest -> begin
(
# 2122 "FStar.ToSMT.Encode.fst"
let _47_3497 = (aux rest)
in (match (_47_3497) with
| (out, rest) -> begin
(
# 2123 "FStar.ToSMT.Encode.fst"
let t = (FStar_Tc_Normalize.norm_typ ((FStar_Tc_Normalize.DeltaHard)::(FStar_Tc_Normalize.Beta)::(FStar_Tc_Normalize.Eta)::(FStar_Tc_Normalize.EtaArgs)::(FStar_Tc_Normalize.Simplify)::[]) env.tcenv t)
in (let _126_2385 = (let _126_2384 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_126_2384)::out)
in (_126_2385, rest)))
end))
end
| FStar_Tc_Env.Binding_typ (a, k)::rest -> begin
(
# 2126 "FStar.ToSMT.Encode.fst"
let _47_3507 = (aux rest)
in (match (_47_3507) with
| (out, rest) -> begin
(let _126_2387 = (let _126_2386 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_126_2386)::out)
in (_126_2387, rest))
end))
end
| _47_3509 -> begin
([], bindings)
end))
in (
# 2129 "FStar.ToSMT.Encode.fst"
let _47_3512 = (aux bindings)
in (match (_47_3512) with
| (closing, bindings) -> begin
(let _126_2388 = (FStar_Absyn_Util.close_forall (FStar_List.rev closing) q)
in (_126_2388, bindings))
end)))
in (match (_47_3515) with
| (q, bindings) -> begin
(
# 2131 "FStar.ToSMT.Encode.fst"
let _47_3524 = (let _126_2390 = (FStar_List.filter (fun _47_32 -> (match (_47_32) with
| FStar_Tc_Env.Binding_sig (_47_3518) -> begin
false
end
| _47_3521 -> begin
true
end)) bindings)
in (encode_env_bindings env _126_2390))
in (match (_47_3524) with
| (env_decls, env) -> begin
(
# 2132 "FStar.ToSMT.Encode.fst"
let _47_3525 = if (FStar_Tc_Env.debug tcenv FStar_Options.Low) then begin
(let _126_2391 = (FStar_Absyn_Print.formula_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" _126_2391))
end else begin
()
end
in (
# 2133 "FStar.ToSMT.Encode.fst"
let _47_3530 = (encode_formula_with_labels q env)
in (match (_47_3530) with
| (phi, labels, qdecls) -> begin
(
# 2134 "FStar.ToSMT.Encode.fst"
let _47_3533 = (encode_labels labels)
in (match (_47_3533) with
| (label_prefix, label_suffix) -> begin
(
# 2135 "FStar.ToSMT.Encode.fst"
let query_prelude = (FStar_List.append (FStar_List.append env_decls label_prefix) qdecls)
in (
# 2139 "FStar.ToSMT.Encode.fst"
let qry = (let _126_2393 = (let _126_2392 = (FStar_ToSMT_Term.mkNot phi)
in (_126_2392, Some ("query")))
in FStar_ToSMT_Term.Assume (_126_2393))
in (
# 2140 "FStar.ToSMT.Encode.fst"
let suffix = (FStar_List.append label_suffix ((FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))
end))))
in (match (_47_3541) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| FStar_ToSMT_Term.Assume ({FStar_ToSMT_Term.tm = FStar_ToSMT_Term.App (FStar_ToSMT_Term.False, _47_3548); FStar_ToSMT_Term.hash = _47_3545; FStar_ToSMT_Term.freevars = _47_3543}, _47_3553) -> begin
(
# 2143 "FStar.ToSMT.Encode.fst"
let _47_3556 = (pop ())
in ())
end
| _47_3559 when tcenv.FStar_Tc_Env.admit -> begin
(
# 2144 "FStar.ToSMT.Encode.fst"
let _47_3560 = (pop ())
in ())
end
| FStar_ToSMT_Term.Assume (q, _47_3564) -> begin
(
# 2146 "FStar.ToSMT.Encode.fst"
let fresh = ((FStar_String.length q.FStar_ToSMT_Term.hash) >= 2048)
in (
# 2147 "FStar.ToSMT.Encode.fst"
let _47_3568 = (FStar_ToSMT_Z3.giveZ3 prefix)
in (
# 2149 "FStar.ToSMT.Encode.fst"
let with_fuel = (fun p _47_3574 -> (match (_47_3574) with
| (n, i) -> begin
(let _126_2416 = (let _126_2415 = (let _126_2400 = (let _126_2399 = (FStar_Util.string_of_int n)
in (let _126_2398 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _126_2399 _126_2398)))
in FStar_ToSMT_Term.Caption (_126_2400))
in (let _126_2414 = (let _126_2413 = (let _126_2405 = (let _126_2404 = (let _126_2403 = (let _126_2402 = (FStar_ToSMT_Term.mkApp ("MaxFuel", []))
in (let _126_2401 = (FStar_ToSMT_Term.n_fuel n)
in (_126_2402, _126_2401)))
in (FStar_ToSMT_Term.mkEq _126_2403))
in (_126_2404, None))
in FStar_ToSMT_Term.Assume (_126_2405))
in (let _126_2412 = (let _126_2411 = (let _126_2410 = (let _126_2409 = (let _126_2408 = (let _126_2407 = (FStar_ToSMT_Term.mkApp ("MaxIFuel", []))
in (let _126_2406 = (FStar_ToSMT_Term.n_fuel i)
in (_126_2407, _126_2406)))
in (FStar_ToSMT_Term.mkEq _126_2408))
in (_126_2409, None))
in FStar_ToSMT_Term.Assume (_126_2410))
in (_126_2411)::(p)::(FStar_ToSMT_Term.CheckSat)::[])
in (_126_2413)::_126_2412))
in (_126_2415)::_126_2414))
in (FStar_List.append _126_2416 suffix))
end))
in (
# 2156 "FStar.ToSMT.Encode.fst"
let check = (fun p -> (
# 2157 "FStar.ToSMT.Encode.fst"
let initial_config = (let _126_2420 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _126_2419 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_126_2420, _126_2419)))
in (
# 2158 "FStar.ToSMT.Encode.fst"
let alt_configs = (let _126_2439 = (let _126_2438 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _126_2423 = (let _126_2422 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _126_2421 = (FStar_ST.read FStar_Options.max_ifuel)
in (_126_2422, _126_2421)))
in (_126_2423)::[])
end else begin
[]
end
in (let _126_2437 = (let _126_2436 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _126_2426 = (let _126_2425 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _126_2424 = (FStar_ST.read FStar_Options.max_ifuel)
in (_126_2425, _126_2424)))
in (_126_2426)::[])
end else begin
[]
end
in (let _126_2435 = (let _126_2434 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _126_2429 = (let _126_2428 = (FStar_ST.read FStar_Options.max_fuel)
in (let _126_2427 = (FStar_ST.read FStar_Options.max_ifuel)
in (_126_2428, _126_2427)))
in (_126_2429)::[])
end else begin
[]
end
in (let _126_2433 = (let _126_2432 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _126_2431 = (let _126_2430 = (FStar_ST.read FStar_Options.min_fuel)
in (_126_2430, 1))
in (_126_2431)::[])
end else begin
[]
end
in (_126_2432)::[])
in (_126_2434)::_126_2433))
in (_126_2436)::_126_2435))
in (_126_2438)::_126_2437))
in (FStar_List.flatten _126_2439))
in (
# 2163 "FStar.ToSMT.Encode.fst"
let report = (fun errs -> (
# 2164 "FStar.ToSMT.Encode.fst"
let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", FStar_Absyn_Syntax.dummyRange))::[]
end
| _47_3583 -> begin
errs
end)
in (
# 2167 "FStar.ToSMT.Encode.fst"
let _47_3585 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _126_2447 = (let _126_2442 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _126_2442))
in (let _126_2446 = (let _126_2443 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _126_2443 FStar_Util.string_of_int))
in (let _126_2445 = (let _126_2444 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _126_2444 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _126_2447 _126_2446 _126_2445))))
end else begin
()
end
in (FStar_Tc_Errors.add_errors tcenv errs))))
in (
# 2174 "FStar.ToSMT.Encode.fst"
let rec try_alt_configs = (fun p errs _47_33 -> (match (_47_33) with
| [] -> begin
(report errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _126_2458 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _126_2458 (cb mi p [])))
end
| _47_3597 -> begin
(report errs)
end)
end
| mi::tl -> begin
(let _126_2460 = (with_fuel p mi)
in (FStar_ToSMT_Z3.ask fresh labels _126_2460 (fun _47_3603 -> (match (_47_3603) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _47_3606 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end))
and cb = (fun _47_3609 p alt _47_3614 -> (match ((_47_3609, _47_3614)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _126_2468 = (let _126_2465 = (FStar_Tc_Env.get_range tcenv)
in (FStar_Range.string_of_range _126_2465))
in (let _126_2467 = (FStar_Util.string_of_int prev_fuel)
in (let _126_2466 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _126_2468 _126_2467 _126_2466))))
end else begin
()
end
end else begin
(try_alt_configs p errs alt)
end
end))
in (let _126_2469 = (with_fuel p initial_config)
in (FStar_ToSMT_Z3.ask fresh labels _126_2469 (cb initial_config p alt_configs))))))))
in (
# 2199 "FStar.ToSMT.Encode.fst"
let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 2201 "FStar.ToSMT.Encode.fst"
let _47_3619 = (let _126_2475 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_ToSMT_SplitQueryCases.can_handle_query _126_2475 q))
in (match (_47_3619) with
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
# 2206 "FStar.ToSMT.Encode.fst"
let _47_3620 = if (FStar_ST.read FStar_Options.admit_smt_queries) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end)
end)))))

# 2210 "FStar.ToSMT.Encode.fst"
let is_trivial : FStar_Tc_Env.env  ->  FStar_Absyn_Syntax.typ  ->  Prims.bool = (fun tcenv q -> (
# 2211 "FStar.ToSMT.Encode.fst"
let env = (get_env tcenv)
in (
# 2212 "FStar.ToSMT.Encode.fst"
let _47_3625 = (push "query")
in (
# 2213 "FStar.ToSMT.Encode.fst"
let _47_3632 = (encode_formula_with_labels q env)
in (match (_47_3632) with
| (f, _47_3629, _47_3631) -> begin
(
# 2214 "FStar.ToSMT.Encode.fst"
let _47_3633 = (pop "query")
in (match (f.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.True, _47_3637) -> begin
true
end
| _47_3641 -> begin
false
end))
end)))))

# 2219 "FStar.ToSMT.Encode.fst"
let solver : FStar_Tc_Env.solver_t = {FStar_Tc_Env.init = init; FStar_Tc_Env.push = push; FStar_Tc_Env.pop = pop; FStar_Tc_Env.mark = mark; FStar_Tc_Env.reset_mark = reset_mark; FStar_Tc_Env.commit_mark = commit_mark; FStar_Tc_Env.encode_modul = encode_modul; FStar_Tc_Env.encode_sig = encode_sig; FStar_Tc_Env.solve = solve; FStar_Tc_Env.is_trivial = is_trivial; FStar_Tc_Env.finish = FStar_ToSMT_Z3.finish; FStar_Tc_Env.refresh = FStar_ToSMT_Z3.refresh}

# 2233 "FStar.ToSMT.Encode.fst"
let dummy : FStar_Tc_Env.solver_t = {FStar_Tc_Env.init = (fun _47_3642 -> ()); FStar_Tc_Env.push = (fun _47_3644 -> ()); FStar_Tc_Env.pop = (fun _47_3646 -> ()); FStar_Tc_Env.mark = (fun _47_3648 -> ()); FStar_Tc_Env.reset_mark = (fun _47_3650 -> ()); FStar_Tc_Env.commit_mark = (fun _47_3652 -> ()); FStar_Tc_Env.encode_modul = (fun _47_3654 _47_3656 -> ()); FStar_Tc_Env.encode_sig = (fun _47_3658 _47_3660 -> ()); FStar_Tc_Env.solve = (fun _47_3662 _47_3664 -> ()); FStar_Tc_Env.is_trivial = (fun _47_3666 _47_3668 -> false); FStar_Tc_Env.finish = (fun _47_3670 -> ()); FStar_Tc_Env.refresh = (fun _47_3671 -> ())}






let add_fuel = (fun x tl -> if (! (Microsoft_FStar_Options.unthrottle_inductives)) then begin
tl
end else begin
(x)::tl
end)

let withenv = (fun c _45_39 -> (match (_45_39) with
| (a, b) -> begin
(a, b, c)
end))

let vargs = (fun args -> (Support.List.filter (fun _45_1 -> (match (_45_1) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
false
end
| _ -> begin
true
end)) args))

let escape = (fun s -> (Support.Microsoft.FStar.Util.replace_char s '\'' '_'))

let escape_null_name = (fun a -> if (a.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText = "_") then begin
(Support.String.strcat a.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText a.Microsoft_FStar_Absyn_Syntax.realname.Microsoft_FStar_Absyn_Syntax.idText)
end else begin
a.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText
end)

let mk_typ_projector_name = (fun lid a -> (escape (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a))))

let mk_term_projector_name = (fun lid a -> (let a = {Microsoft_FStar_Absyn_Syntax.ppname = (Microsoft_FStar_Absyn_Util.unmangle_field_name a.Microsoft_FStar_Absyn_Syntax.ppname); Microsoft_FStar_Absyn_Syntax.realname = a.Microsoft_FStar_Absyn_Syntax.realname}
in (escape (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (escape_null_name a)))))

let primitive_projector_by_pos = (fun env lid i -> (let fail = (fun _45_61 -> (match (_45_61) with
| () -> begin
(failwith (Support.Microsoft.FStar.Util.format2 "Projector %s on data constructor %s not found" (Support.Microsoft.FStar.Util.string_of_int i) lid.Microsoft_FStar_Absyn_Syntax.str))
end))
in (let t = (Microsoft_FStar_Tc_Env.lookup_datacon env lid)
in (match ((Microsoft_FStar_Absyn_Util.compress_typ t).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, _)) -> begin
if ((i < 0) || (i >= (Support.List.length binders))) then begin
(fail ())
end else begin
(let b = (Support.List.nth binders i)
in (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(mk_typ_projector_name lid a.Microsoft_FStar_Absyn_Syntax.v)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(mk_term_projector_name lid x.Microsoft_FStar_Absyn_Syntax.v)
end))
end
end
| _ -> begin
(fail ())
end))))

let mk_term_projector_name_by_pos = (fun lid i -> (escape (Support.Microsoft.FStar.Util.format2 "%s_%s" lid.Microsoft_FStar_Absyn_Syntax.str (Support.Microsoft.FStar.Util.string_of_int i))))

let mk_typ_projector = (fun lid a -> (Microsoft_FStar_ToSMT_Term.mkFreeV ((mk_typ_projector_name lid a), Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Type_sort)))))

let mk_term_projector = (fun lid a -> (Microsoft_FStar_ToSMT_Term.mkFreeV ((mk_term_projector_name lid a), Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort)))))

let mk_term_projector_by_pos = (fun lid i -> (Microsoft_FStar_ToSMT_Term.mkFreeV ((mk_term_projector_name_by_pos lid i), Microsoft_FStar_ToSMT_Term.Arrow ((Microsoft_FStar_ToSMT_Term.Term_sort, Microsoft_FStar_ToSMT_Term.Term_sort)))))

let mk_data_tester = (fun env l x -> (Microsoft_FStar_ToSMT_Term.mk_tester (escape l.Microsoft_FStar_Absyn_Syntax.str) x))

type varops_t =
{push : unit  ->  unit; pop : unit  ->  unit; mark : unit  ->  unit; reset_mark : unit  ->  unit; commit_mark : unit  ->  unit; new_var : Microsoft_FStar_Absyn_Syntax.ident  ->  Microsoft_FStar_Absyn_Syntax.ident  ->  string; new_fvar : Microsoft_FStar_Absyn_Syntax.lident  ->  string; fresh : string  ->  string; string_const : string  ->  Microsoft_FStar_ToSMT_Term.term; next_id : unit  ->  int}

let varops = (let initial_ctr = 10
in (let ctr = (Support.Microsoft.FStar.Util.mk_ref initial_ctr)
in (let new_scope = (fun _45_100 -> (match (_45_100) with
| () -> begin
((Support.Microsoft.FStar.Util.smap_create 100), (Support.Microsoft.FStar.Util.smap_create 100))
end))
in (let scopes = (Support.Microsoft.FStar.Util.mk_ref (((new_scope ()))::[]))
in (let mk_unique = (fun y -> (let y = (escape y)
in (let y = (match ((Support.Microsoft.FStar.Util.find_map (! (scopes)) (fun _45_108 -> (match (_45_108) with
| (names, _) -> begin
(Support.Microsoft.FStar.Util.smap_try_find names y)
end)))) with
| None -> begin
y
end
| Some (_) -> begin
(let _45_113 = (Support.Microsoft.FStar.Util.incr ctr)
in (Support.String.strcat (Support.String.strcat y "__") (Support.Microsoft.FStar.Util.string_of_int (! (ctr)))))
end)
in (let top_scope = ((Support.Prims.fst) (Support.List.hd (! (scopes))))
in (let _45_117 = (Support.Microsoft.FStar.Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun pp rn -> (Support.String.strcat (Support.String.strcat (mk_unique pp.Microsoft_FStar_Absyn_Syntax.idText) "__") rn.Microsoft_FStar_Absyn_Syntax.idText))
in (let new_fvar = (fun lid -> (mk_unique lid.Microsoft_FStar_Absyn_Syntax.str))
in (let next_id = (fun _45_125 -> (match (_45_125) with
| () -> begin
(let _45_126 = (Support.Microsoft.FStar.Util.incr ctr)
in (! (ctr)))
end))
in (let fresh = (fun pfx -> (Support.Microsoft.FStar.Util.format2 "%s_%s" pfx (Support.Microsoft.FStar.Util.string_of_int (next_id ()))))
in (let string_const = (fun s -> (match ((Support.Microsoft.FStar.Util.find_map (! (scopes)) (fun _45_135 -> (match (_45_135) with
| (_, strings) -> begin
(Support.Microsoft.FStar.Util.smap_try_find strings s)
end)))) with
| Some (f) -> begin
f
end
| None -> begin
(let id = (next_id ())
in (let f = (Microsoft_FStar_ToSMT_Term.boxString (Microsoft_FStar_ToSMT_Term.mk_String_const id))
in (let top_scope = ((Support.Prims.snd) (Support.List.hd (! (scopes))))
in (let _45_142 = (Support.Microsoft.FStar.Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun _45_145 -> (match (_45_145) with
| () -> begin
(scopes := ((new_scope ()))::(! (scopes)))
end))
in (let pop = (fun _45_147 -> (match (_45_147) with
| () -> begin
(scopes := (Support.List.tl (! (scopes))))
end))
in (let mark = (fun _45_149 -> (match (_45_149) with
| () -> begin
(push ())
end))
in (let reset_mark = (fun _45_151 -> (match (_45_151) with
| () -> begin
(pop ())
end))
in (let commit_mark = (fun _45_153 -> (match (_45_153) with
| () -> begin
(match ((! (scopes))) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(let _45_166 = (Support.Microsoft.FStar.Util.smap_fold hd1 (fun key value v -> (Support.Microsoft.FStar.Util.smap_add next1 key value)) ())
in (let _45_171 = (Support.Microsoft.FStar.Util.smap_fold hd2 (fun key value v -> (Support.Microsoft.FStar.Util.smap_add next2 key value)) ())
in (scopes := ((next1, next2))::tl)))
end
| _ -> begin
(failwith "Impossible")
end)
end))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id})))))))))))))))

let unmangle = (fun x -> (Microsoft_FStar_Absyn_Util.mkbvd ((Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.ppname), (Microsoft_FStar_Absyn_Util.unmangle_field_name x.Microsoft_FStar_Absyn_Syntax.realname))))

type binding =
| Binding_var of (Microsoft_FStar_Absyn_Syntax.bvvdef * Microsoft_FStar_ToSMT_Term.term)
| Binding_tvar of (Microsoft_FStar_Absyn_Syntax.btvdef * Microsoft_FStar_ToSMT_Term.term)
| Binding_fvar of (Microsoft_FStar_Absyn_Syntax.lident * string * Microsoft_FStar_ToSMT_Term.term option * Microsoft_FStar_ToSMT_Term.term option)
| Binding_ftvar of (Microsoft_FStar_Absyn_Syntax.lident * string * Microsoft_FStar_ToSMT_Term.term option)

let binder_of_eithervar = (fun v -> (v, None))

type env_t =
{bindings : binding list; depth : int; tcenv : Microsoft_FStar_Tc_Env.env; warn : bool; cache : (string * Microsoft_FStar_ToSMT_Term.sort list * Microsoft_FStar_ToSMT_Term.decl list) Support.Microsoft.FStar.Util.smap; nolabels : bool; use_zfuel_name : bool}

let print_env = (fun e -> ((Support.String.concat ", ") ((Support.List.map (fun _45_2 -> (match (_45_2) with
| Binding_var ((x, t)) -> begin
(Microsoft_FStar_Absyn_Print.strBvd x)
end
| Binding_tvar ((a, t)) -> begin
(Microsoft_FStar_Absyn_Print.strBvd a)
end
| Binding_fvar ((l, s, t, _)) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end
| Binding_ftvar ((l, s, t)) -> begin
(Microsoft_FStar_Absyn_Print.sli l)
end))) e.bindings)))

let lookup_binding = (fun env f -> (Support.Microsoft.FStar.Util.find_map env.bindings f))

let caption_t = (fun env t -> if (Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low) then begin
Some ((Microsoft_FStar_Absyn_Print.typ_to_string t))
end else begin
None
end)

let fresh_fvar = (fun x s -> (let xsym = (varops.fresh x)
in (xsym, (Microsoft_FStar_ToSMT_Term.mkFreeV (xsym, s)))))

let gen_term_var = (fun env x -> (let ysym = (Support.String.strcat "@x" (Support.Microsoft.FStar.Util.string_of_int env.depth))
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV (ysym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (ysym, y, (let _45_227 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _45_227.tcenv; warn = _45_227.warn; cache = _45_227.cache; nolabels = _45_227.nolabels; use_zfuel_name = _45_227.use_zfuel_name})))))

let new_term_constant = (fun env x -> (let ysym = (varops.new_var x.Microsoft_FStar_Absyn_Syntax.ppname x.Microsoft_FStar_Absyn_Syntax.realname)
in (let y = (Microsoft_FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _45_233 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _45_233.depth; tcenv = _45_233.tcenv; warn = _45_233.warn; cache = _45_233.cache; nolabels = _45_233.nolabels; use_zfuel_name = _45_233.use_zfuel_name})))))

let push_term_var = (fun env x t -> (let _45_238 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _45_238.depth; tcenv = _45_238.tcenv; warn = _45_238.warn; cache = _45_238.cache; nolabels = _45_238.nolabels; use_zfuel_name = _45_238.use_zfuel_name}))

let lookup_term_var = (fun env a -> (match ((lookup_binding env (fun _45_3 -> (match (_45_3) with
| Binding_var ((b, t)) when (Microsoft_FStar_Absyn_Util.bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _ -> begin
None
end)))) with
| None -> begin
(failwith (Support.Microsoft.FStar.Util.format1 "Bound term variable not found: %s" (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)))
end
| Some ((b, t)) -> begin
t
end))

let gen_typ_var = (fun env x -> (let ysym = (Support.String.strcat "@a" (Support.Microsoft.FStar.Util.string_of_int env.depth))
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV (ysym, Microsoft_FStar_ToSMT_Term.Type_sort))
in (ysym, y, (let _45_258 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _45_258.tcenv; warn = _45_258.warn; cache = _45_258.cache; nolabels = _45_258.nolabels; use_zfuel_name = _45_258.use_zfuel_name})))))

let new_typ_constant = (fun env x -> (let ysym = (varops.new_var x.Microsoft_FStar_Absyn_Syntax.ppname x.Microsoft_FStar_Absyn_Syntax.realname)
in (let y = (Microsoft_FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _45_264 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = _45_264.depth; tcenv = _45_264.tcenv; warn = _45_264.warn; cache = _45_264.cache; nolabels = _45_264.nolabels; use_zfuel_name = _45_264.use_zfuel_name})))))

let push_typ_var = (fun env x t -> (let _45_269 = env
in {bindings = (Binding_tvar ((x, t)))::env.bindings; depth = _45_269.depth; tcenv = _45_269.tcenv; warn = _45_269.warn; cache = _45_269.cache; nolabels = _45_269.nolabels; use_zfuel_name = _45_269.use_zfuel_name}))

let lookup_typ_var = (fun env a -> (match ((lookup_binding env (fun _45_4 -> (match (_45_4) with
| Binding_tvar ((b, t)) when (Microsoft_FStar_Absyn_Util.bvd_eq b a.Microsoft_FStar_Absyn_Syntax.v) -> begin
Some ((b, t))
end
| _ -> begin
None
end)))) with
| None -> begin
(failwith (Support.Microsoft.FStar.Util.format1 "Bound type variable not found: %s" (Microsoft_FStar_Absyn_Print.strBvd a.Microsoft_FStar_Absyn_Syntax.v)))
end
| Some ((b, t)) -> begin
t
end))

let new_term_constant_and_tok_from_lid = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Support.String.strcat fname "@tok")
in (fname, ftok, (let _45_289 = env
in {bindings = (Binding_fvar ((x, fname, ((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))), None)))::env.bindings; depth = _45_289.depth; tcenv = _45_289.tcenv; warn = _45_289.warn; cache = _45_289.cache; nolabels = _45_289.nolabels; use_zfuel_name = _45_289.use_zfuel_name})))))

let try_lookup_lid = (fun env a -> (lookup_binding env (fun _45_5 -> (match (_45_5) with
| Binding_fvar ((b, t1, t2, t3)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2, t3))
end
| _ -> begin
None
end))))

let lookup_lid = (fun env a -> (match ((try_lookup_lid env a)) with
| None -> begin
(failwith (Support.Microsoft.FStar.Util.format1 "Name not found: %s" (Microsoft_FStar_Absyn_Print.sli a)))
end
| Some (s) -> begin
s
end))

let push_free_var = (fun env x fname ftok -> (let _45_311 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _45_311.depth; tcenv = _45_311.tcenv; warn = _45_311.warn; cache = _45_311.cache; nolabels = _45_311.nolabels; use_zfuel_name = _45_311.use_zfuel_name}))

let push_zfuel_name = (fun env x f -> (let _45_320 = (lookup_lid env x)
in (match (_45_320) with
| (t1, t2, _) -> begin
(let t3 = (Microsoft_FStar_ToSMT_Term.mkApp (f, ((Microsoft_FStar_ToSMT_Term.mkApp ("ZFuel", [])))::[]))
in (let _45_322 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _45_322.depth; tcenv = _45_322.tcenv; warn = _45_322.warn; cache = _45_322.cache; nolabels = _45_322.nolabels; use_zfuel_name = _45_322.use_zfuel_name}))
end)))

let lookup_free_var = (fun env a -> (let _45_329 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_45_329) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
f
end
| _ -> begin
(match (sym) with
| Some (t) -> begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((_, fuel::[])) -> begin
if (Support.Microsoft.FStar.Util.starts_with ((Support.Prims.fst) (Microsoft_FStar_ToSMT_Term.fv_of_term fuel)) "fuel") then begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyEF (Microsoft_FStar_ToSMT_Term.mkFreeV (name, Microsoft_FStar_ToSMT_Term.Term_sort)) fuel)
end else begin
t
end
end
| _ -> begin
t
end)
end
| _ -> begin
(failwith (Support.Microsoft.FStar.Util.format1 "Name not found: %s" (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)))
end)
end)
end)))

let lookup_free_var_name = (fun env a -> (let _45_353 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_45_353) with
| (x, _, _) -> begin
x
end)))

let lookup_free_var_sym = (fun env a -> (let _45_359 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_45_359) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.App ((g, zf)); Microsoft_FStar_ToSMT_Term.hash = _; Microsoft_FStar_ToSMT_Term.freevars = _}) when env.use_zfuel_name -> begin
(g, zf)
end
| _ -> begin
(match (sym) with
| None -> begin
(Microsoft_FStar_ToSMT_Term.Var (name), [])
end
| Some (sym) -> begin
(match (sym.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((g, fuel::[])) -> begin
(g, (fuel)::[])
end
| _ -> begin
(Microsoft_FStar_ToSMT_Term.Var (name), [])
end)
end)
end)
end)))

let new_typ_constant_and_tok_from_lid = (fun env x -> (let fname = (varops.new_fvar x)
in (let ftok = (Support.String.strcat fname "@tok")
in (fname, ftok, (let _45_386 = env
in {bindings = (Binding_ftvar ((x, fname, ((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))))))::env.bindings; depth = _45_386.depth; tcenv = _45_386.tcenv; warn = _45_386.warn; cache = _45_386.cache; nolabels = _45_386.nolabels; use_zfuel_name = _45_386.use_zfuel_name})))))

let lookup_tlid = (fun env a -> (match ((lookup_binding env (fun _45_6 -> (match (_45_6) with
| Binding_ftvar ((b, t1, t2)) when (Microsoft_FStar_Absyn_Syntax.lid_equals b a) -> begin
Some ((t1, t2))
end
| _ -> begin
None
end)))) with
| None -> begin
(failwith (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" (Microsoft_FStar_Absyn_Print.sli a)))
end
| Some (s) -> begin
s
end))

let push_free_tvar = (fun env x fname ftok -> (let _45_405 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _45_405.depth; tcenv = _45_405.tcenv; warn = _45_405.warn; cache = _45_405.cache; nolabels = _45_405.nolabels; use_zfuel_name = _45_405.use_zfuel_name}))

let lookup_free_tvar = (fun env a -> (match (((Support.Prims.snd) (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v))) with
| None -> begin
(failwith (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun env a -> ((Support.Prims.fst) (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)))

let tok_of_name = (fun env nm -> (Support.Microsoft.FStar.Util.find_map env.bindings (fun _45_7 -> (match (_45_7) with
| (Binding_fvar ((_, nm', tok, _))) | (Binding_ftvar ((_, nm', tok))) when (nm = nm') -> begin
tok
end
| _ -> begin
None
end))))

let mkForall_fuel' = (fun n _45_435 -> (match (_45_435) with
| (pats, vars, body) -> begin
(let fallback = (fun _45_437 -> (match (_45_437) with
| () -> begin
(Microsoft_FStar_ToSMT_Term.mkForall (pats, vars, body))
end))
in if (! (Microsoft_FStar_Options.unthrottle_inductives)) then begin
(fallback ())
end else begin
(let _45_440 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_45_440) with
| (fsym, fterm) -> begin
(let pats = ((Support.List.map (fun p -> (match (p.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Var ("HasType"), args)) -> begin
(Microsoft_FStar_ToSMT_Term.mkApp ("HasTypeFuel", (fterm)::args))
end
| _ -> begin
p
end))) pats)
in (let vars = ((fsym, Microsoft_FStar_ToSMT_Term.Fuel_sort))::vars
in (Microsoft_FStar_ToSMT_Term.mkForall (pats, vars, body))))
end))
end)
end))

let mkForall_fuel = (mkForall_fuel' 1)

let head_normal = (fun env t -> (let t = (Microsoft_FStar_Absyn_Util.unmeta_typ t)
in (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Typ_fun (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_refine (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_btvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_uvar (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_lam (_)) -> begin
true
end
| (Microsoft_FStar_Absyn_Syntax.Typ_const (v)) | (Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (v); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) -> begin
((Support.Option.isNone) (Microsoft_FStar_Tc_Env.lookup_typ_abbrev env.tcenv v.Microsoft_FStar_Absyn_Syntax.v))
end
| _ -> begin
false
end)))

let whnf = (fun env t -> if (head_normal env t) then begin
t
end else begin
(Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.WHNF)::(Microsoft_FStar_Tc_Normalize.DeltaHard)::[]) env.tcenv t)
end)

let whnf_e = (fun env e -> (Microsoft_FStar_Tc_Normalize.norm_exp ((Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.WHNF)::[]) env.tcenv e))

let norm_t = (fun env t -> (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.Beta)::[]) env.tcenv t))

let norm_k = (fun env k -> (Microsoft_FStar_Tc_Normalize.normalize_kind env.tcenv k))

let trivial_post = (fun t -> (Microsoft_FStar_Absyn_Syntax.mk_Typ_lam (((Microsoft_FStar_Absyn_Syntax.null_v_binder t))::[], (Microsoft_FStar_Absyn_Util.ftv Microsoft_FStar_Absyn_Const.true_lid Microsoft_FStar_Absyn_Syntax.ktype)) None t.Microsoft_FStar_Absyn_Syntax.pos))

let mk_ApplyE = (fun e vars -> ((Support.List.fold_left (fun out var -> (match ((Support.Prims.snd var)) with
| Microsoft_FStar_ToSMT_Term.Type_sort -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyET out (Microsoft_FStar_ToSMT_Term.mkFreeV var))
end
| Microsoft_FStar_ToSMT_Term.Fuel_sort -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyEF out (Microsoft_FStar_ToSMT_Term.mkFreeV var))
end
| _ -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyEE out (Microsoft_FStar_ToSMT_Term.mkFreeV var))
end)) e) vars))

let mk_ApplyE_args = (fun e args -> ((Support.List.fold_left (fun out arg -> (match (arg) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyET out t)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyEE out e)
end)) e) args))

let mk_ApplyT = (fun t vars -> ((Support.List.fold_left (fun out var -> (match ((Support.Prims.snd var)) with
| Microsoft_FStar_ToSMT_Term.Type_sort -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyTT out (Microsoft_FStar_ToSMT_Term.mkFreeV var))
end
| _ -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyTE out (Microsoft_FStar_ToSMT_Term.mkFreeV var))
end)) t) vars))

let mk_ApplyT_args = (fun t args -> ((Support.List.fold_left (fun out arg -> (match (arg) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyTT out t)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(Microsoft_FStar_ToSMT_Term.mk_ApplyTE out e)
end)) t) args))

let is_app = (fun _45_8 -> (match (_45_8) with
| (Microsoft_FStar_ToSMT_Term.Var ("ApplyTT")) | (Microsoft_FStar_ToSMT_Term.Var ("ApplyTE")) | (Microsoft_FStar_ToSMT_Term.Var ("ApplyET")) | (Microsoft_FStar_ToSMT_Term.Var ("ApplyEE")) -> begin
true
end
| _ -> begin
false
end))

let is_eta = (fun env vars t -> (let rec aux = (fun t xs -> (match ((t.Microsoft_FStar_ToSMT_Term.tm, xs)) with
| (Microsoft_FStar_ToSMT_Term.App ((app, f::{Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.FreeV (y); Microsoft_FStar_ToSMT_Term.hash = _; Microsoft_FStar_ToSMT_Term.freevars = _}::[])), x::xs) when ((is_app app) && (Microsoft_FStar_ToSMT_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Var (f), args)), _) -> begin
if (((Support.List.length args) = (Support.List.length vars)) && (Support.List.forall2 (fun a v -> (match (a.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.FreeV (fv) -> begin
(Microsoft_FStar_ToSMT_Term.fv_eq fv v)
end
| _ -> begin
false
end)) args vars)) then begin
(tok_of_name env f)
end else begin
None
end
end
| (_, []) -> begin
(let fvs = (Microsoft_FStar_ToSMT_Term.free_variables t)
in if ((Support.List.for_all (fun fv -> (not ((Support.Microsoft.FStar.Util.for_some (Microsoft_FStar_ToSMT_Term.fv_eq fv) vars))))) fvs) then begin
Some (t)
end else begin
None
end)
end
| _ -> begin
None
end))
in (aux t (Support.List.rev vars))))

type label =
(Microsoft_FStar_ToSMT_Term.fv * string * Support.Microsoft.FStar.Range.range)

type labels =
label list

type pattern =
{pat_vars : (Microsoft_FStar_Absyn_Syntax.either_var * Microsoft_FStar_ToSMT_Term.fv) list; pat_term : unit  ->  (Microsoft_FStar_ToSMT_Term.term * Microsoft_FStar_ToSMT_Term.decls_t); guard : Microsoft_FStar_ToSMT_Term.term  ->  Microsoft_FStar_ToSMT_Term.term; projections : Microsoft_FStar_ToSMT_Term.term  ->  (Microsoft_FStar_Absyn_Syntax.either_var * Microsoft_FStar_ToSMT_Term.term) list}

exception Let_rec_unencodeable

let encode_const = (fun _45_9 -> (match (_45_9) with
| Microsoft_FStar_Absyn_Syntax.Const_unit -> begin
Microsoft_FStar_ToSMT_Term.mk_Term_unit
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (true) -> begin
(Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkTrue)
end
| Microsoft_FStar_Absyn_Syntax.Const_bool (false) -> begin
(Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkFalse)
end
| Microsoft_FStar_Absyn_Syntax.Const_char (c) -> begin
(Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_char c)))
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkInteger' (Support.Microsoft.FStar.Util.int_of_uint8 i)))
end
| Microsoft_FStar_Absyn_Syntax.Const_int (i) -> begin
(Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkInteger i))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (i) -> begin
(Microsoft_FStar_ToSMT_Term.mkApp ("Int32.Int32", ((Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkInteger' i)))::[]))
end
| Microsoft_FStar_Absyn_Syntax.Const_string ((bytes, _)) -> begin
(varops.string_const (Support.Microsoft.FStar.Util.string_of_bytes bytes))
end
| c -> begin
(failwith (Support.Microsoft.FStar.Util.format1 "Unhandled constant: %s\n" (Microsoft_FStar_Absyn_Print.const_to_string c)))
end))

let rec encode_knd' = (fun prekind k env t -> (match ((Microsoft_FStar_Absyn_Util.compress_kind k).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_type -> begin
((Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type), [])
end
| Microsoft_FStar_Absyn_Syntax.Kind_abbrev ((_, k)) -> begin
(encode_knd' prekind k env t)
end
| Microsoft_FStar_Absyn_Syntax.Kind_uvar ((uv, _)) -> begin
(Microsoft_FStar_ToSMT_Term.mkTrue, [])
end
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, k)) -> begin
(let _45_632 = (encode_binders None bs env)
in (match (_45_632) with
| (vars, guards, env', decls, _) -> begin
(let app = (mk_ApplyT t vars)
in (let _45_636 = (encode_knd' prekind k env' app)
in (match (_45_636) with
| (k, decls') -> begin
(let term = (Microsoft_FStar_ToSMT_Term.mkForall ((app)::[], vars, (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l guards), k))))
in (let term = if prekind then begin
(Microsoft_FStar_ToSMT_Term.mkAnd ((Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" (Microsoft_FStar_ToSMT_Term.mk_PreKind t)), term))
end else begin
term
end
in (term, (Support.List.append decls decls'))))
end)))
end))
end
| _ -> begin
(failwith (Support.Microsoft.FStar.Util.format1 "Unknown kind: %s" (Microsoft_FStar_Absyn_Print.kind_to_string k)))
end))
and encode_knd = (fun k env t -> (encode_knd' true k env t))
and encode_binders = (fun fuel_opt bs env -> (let _45_647 = if (Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint1 "Encoding binders %s\n" (Microsoft_FStar_Absyn_Print.binders_to_string ", " bs))
end
in (let _45_695 = ((Support.List.fold_left (fun _45_654 b -> (match (_45_654) with
| (vars, guards, env, decls, names) -> begin
(let _45_689 = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.v = a; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _}) -> begin
(let a = (unmangle a)
in (let _45_666 = (gen_typ_var env a)
in (match (_45_666) with
| (aasym, aa, env') -> begin
(let _45_669 = (encode_knd' false k env aa)
in (match (_45_669) with
| (guard_a_k, decls') -> begin
((aasym, Microsoft_FStar_ToSMT_Term.Type_sort), guard_a_k, env', decls', Support.Microsoft.FStar.Util.Inl (a))
end))
end)))
end
| Support.Microsoft.FStar.Util.Inr ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _}) -> begin
(let x = (unmangle x)
in (let _45_680 = (gen_term_var env x)
in (match (_45_680) with
| (xxsym, xx, env') -> begin
(let _45_683 = (encode_typ_pred' fuel_opt (norm_t env t) env xx)
in (match (_45_683) with
| (guard_x_t, decls') -> begin
((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort), guard_x_t, env', decls', Support.Microsoft.FStar.Util.Inr (x))
end))
end)))
end)
in (match (_45_689) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (Support.List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])) bs)
in (match (_45_695) with
| (vars, guards, env, decls, names) -> begin
((Support.List.rev vars), (Support.List.rev guards), env, decls, (Support.List.rev names))
end))))
and encode_typ_pred' = (fun fuel_opt t env e -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (let _45_703 = (encode_typ_term t env)
in (match (_45_703) with
| (t, decls) -> begin
((Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel fuel_opt e t), decls)
end))))
and encode_typ_term = (fun t env -> (let t0 = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (match (t0.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
((lookup_typ_var env a), [])
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
((lookup_free_tvar env fv), [])
end
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, res)) -> begin
if (Microsoft_FStar_Absyn_Util.is_tot_or_gtot_comp res) then begin
(let _45_721 = (encode_binders None binders env)
in (match (_45_721) with
| (vars, guards, env', decls, _) -> begin
(let fsym = ((varops.fresh "f"), Microsoft_FStar_ToSMT_Term.Term_sort)
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let app = (mk_ApplyE f vars)
in (let _45_727 = (encode_typ_pred' None (Microsoft_FStar_Absyn_Util.comp_result res) env' app)
in (match (_45_727) with
| (res_pred, decls') -> begin
(let t_interp = (Microsoft_FStar_ToSMT_Term.mkForall ((app)::[], vars, (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l guards), res_pred))))
in (let cvars = ((Support.List.filter (fun _45_732 -> (match (_45_732) with
| (x, _) -> begin
(x <> (Support.Prims.fst fsym))
end))) (Microsoft_FStar_ToSMT_Term.free_variables t_interp))
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (fsym)::cvars, t_interp))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t', sorts, _)) -> begin
((Microsoft_FStar_ToSMT_Term.mkApp (t', ((Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV) cvars))), [])
end
| None -> begin
(let tsym = (varops.fresh "Typ_fun")
in (let cvar_sorts = (Support.List.map (Support.Prims.snd) cvars)
in (let caption = if (! (Microsoft_FStar_Options.logQueries)) then begin
Some ((Microsoft_FStar_Tc_Normalize.typ_norm_to_string env.tcenv t0))
end else begin
None
end
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, caption))
in (let t = (Microsoft_FStar_ToSMT_Term.mkApp (tsym, (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)))
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let k_assumption = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind)), Some ((Support.String.strcat tsym " kinding"))))
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let pre_typing = Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel ((f_has_t)::[], (fsym)::cvars, (Microsoft_FStar_ToSMT_Term.mkImp (f_has_t, (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" (Microsoft_FStar_ToSMT_Term.mk_PreType f)))))), Some ("pre-typing for functions")))
in (let t_interp = Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel ((f_has_t)::[], (fsym)::cvars, (Microsoft_FStar_ToSMT_Term.mkIff (f_has_t, t_interp)))), Some ((Support.String.strcat tsym " interpretation"))))
in (let t_decls = (Support.List.append (Support.List.append decls decls') ((tdecl)::(k_assumption)::(pre_typing)::(t_interp)::[]))
in (let _45_753 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))))
end))))
end)))))
end))
end else begin
(let tsym = (varops.fresh "Non_total_Typ_fun")
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let t = (Microsoft_FStar_ToSMT_Term.mkApp (tsym, []))
in (let t_kinding = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type), None))
in (let fsym = ("f", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let f_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType f t)
in (let t_interp = Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel ((f_has_t)::[], (fsym)::[], (Microsoft_FStar_ToSMT_Term.mkImp (f_has_t, (Microsoft_FStar_ToSMT_Term.mk_tester "Typ_fun" (Microsoft_FStar_ToSMT_Term.mk_PreType f)))))), Some ("pre-typing")))
in (t, (tdecl)::(t_kinding)::(t_interp)::[])))))))))
end
end
| Microsoft_FStar_Absyn_Syntax.Typ_refine (_) -> begin
(let _45_783 = (match ((Microsoft_FStar_Tc_Normalize.normalize_refinement env.tcenv t0)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, f)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
(x, f)
end
| _ -> begin
(failwith "impossible")
end)
in (match (_45_783) with
| (x, f) -> begin
(let _45_786 = (encode_typ_term x.Microsoft_FStar_Absyn_Syntax.sort env)
in (match (_45_786) with
| (base_t, decls) -> begin
(let _45_790 = (gen_term_var env x.Microsoft_FStar_Absyn_Syntax.v)
in (match (_45_790) with
| (x, xtm, env') -> begin
(let _45_793 = (encode_formula f env')
in (match (_45_793) with
| (refinement, decls') -> begin
(let encoding = (Microsoft_FStar_ToSMT_Term.mkAnd ((Microsoft_FStar_ToSMT_Term.mk_HasType xtm base_t), refinement))
in (let cvars = ((Support.List.filter (fun _45_798 -> (match (_45_798) with
| (y, _) -> begin
(y <> x)
end))) (Microsoft_FStar_ToSMT_Term.free_variables encoding))
in (let xfv = (x, Microsoft_FStar_ToSMT_Term.Term_sort)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], (xfv)::cvars, encoding))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _, _)) -> begin
((Microsoft_FStar_ToSMT_Term.mkApp (t, ((Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV) cvars))), [])
end
| None -> begin
(let tsym = (varops.fresh "Typ_refine")
in (let cvar_sorts = (Support.List.map (Support.Prims.snd) cvars)
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let t = (Microsoft_FStar_ToSMT_Term.mkApp (tsym, (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)))
in (let x_has_t = (Microsoft_FStar_ToSMT_Term.mk_HasType xtm t)
in (let t_has_kind = (Microsoft_FStar_ToSMT_Term.mk_HasKind t Microsoft_FStar_ToSMT_Term.mk_Kind_type)
in (let t_kinding = (Microsoft_FStar_ToSMT_Term.mkForall ((t_has_kind)::[], cvars, t_has_kind))
in (let assumption = (mkForall_fuel ((x_has_t)::[], (xfv)::cvars, (Microsoft_FStar_ToSMT_Term.mkIff (x_has_t, encoding))))
in (let t_decls = (Support.List.append (Support.List.append decls decls') ((tdecl)::(Microsoft_FStar_ToSMT_Term.Assume ((t_kinding, None)))::(Microsoft_FStar_ToSMT_Term.Assume ((assumption, Some ((Microsoft_FStar_Absyn_Print.typ_to_string t0)))))::[]))
in (let _45_819 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end)))))
end))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(let ttm = (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar (Support.Microsoft.FStar.Unionfind.uvar_id uv))
in (let _45_828 = (encode_knd k env ttm)
in (match (_45_828) with
| (t_has_k, decls) -> begin
(let d = Microsoft_FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let is_full_app = (fun _45_835 -> (match (_45_835) with
| () -> begin
(let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind head)
in (let _45_840 = (Microsoft_FStar_Absyn_Util.kind_formals kk)
in (match (_45_840) with
| (formals, _) -> begin
((Support.List.length formals) = (Support.List.length args))
end)))
end))
in (let head = (Microsoft_FStar_Absyn_Util.compress_typ head)
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let head = (lookup_typ_var env a)
in (let _45_847 = (encode_args args env)
in (match (_45_847) with
| (args, decls) -> begin
(let t = (mk_ApplyT_args head args)
in (t, decls))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _45_853 = (encode_args args env)
in (match (_45_853) with
| (args, decls) -> begin
if (is_full_app ()) then begin
(let head = (lookup_free_tvar_name env fv)
in (let t = (Microsoft_FStar_ToSMT_Term.mkApp (head, (Support.List.map (fun _45_10 -> (match (_45_10) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args)))
in (t, decls)))
end else begin
(let head = (lookup_free_tvar env fv)
in (let t = (mk_ApplyT_args head args)
in (t, decls)))
end
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(let ttm = (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar (Support.Microsoft.FStar.Unionfind.uvar_id uv))
in (let _45_869 = (encode_knd k env ttm)
in (match (_45_869) with
| (t_has_k, decls) -> begin
(let d = Microsoft_FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| _ -> begin
(let t = (norm_t env t)
in (encode_typ_term t env))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((bs, body)) -> begin
(let _45_884 = (encode_binders None bs env)
in (match (_45_884) with
| (vars, guards, env, decls, _) -> begin
(let _45_887 = (encode_typ_term body env)
in (match (_45_887) with
| (body, decls') -> begin
(let key_body = (Microsoft_FStar_ToSMT_Term.mkForall ([], vars, (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l guards), body))))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _, _)) -> begin
((Microsoft_FStar_ToSMT_Term.mkApp (t, (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars))), [])
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (head) -> begin
(head, [])
end
| None -> begin
(let cvar_sorts = (Support.List.map (Support.Prims.snd) cvars)
in (let tsym = (varops.fresh "Typ_lam")
in (let tdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((tsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let t = (Microsoft_FStar_ToSMT_Term.mkApp (tsym, (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)))
in (let app = (mk_ApplyT t vars)
in (let interp = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((app)::[], (Support.List.append vars cvars), (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l guards), (Microsoft_FStar_ToSMT_Term.mkEq (app, body)))))), Some ("Typ_lam interpretation")))
in (let kinding = (let _45_910 = (encode_knd (Microsoft_FStar_Tc_Recheck.recompute_kind t0) env t)
in (match (_45_910) with
| (ktm, decls'') -> begin
(Support.List.append decls'' ((Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((t)::[], cvars, ktm)), Some ("Typ_lam kinding"))))::[]))
end))
in (let t_decls = (Support.List.append (Support.List.append decls decls') ((tdecl)::(interp)::kinding))
in (let _45_913 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))
end)
end))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _)) -> begin
(encode_typ_term t env)
end
| Microsoft_FStar_Absyn_Syntax.Typ_meta (_) -> begin
(encode_typ_term (Microsoft_FStar_Absyn_Util.unmeta_typ t0) env)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) -> begin
(failwith (Support.Microsoft.FStar.Util.format4 "(%s) Impossible: %s\n%s\n%s\n" (Support.Microsoft.FStar.Range.string_of_range t.Microsoft_FStar_Absyn_Syntax.pos) (Microsoft_FStar_Absyn_Print.tag_of_typ t0) (Microsoft_FStar_Absyn_Print.typ_to_string t0) (Microsoft_FStar_Absyn_Print.typ_to_string t)))
end)))
and encode_exp = (fun e env -> (let e = (Microsoft_FStar_Absyn_Visit.compress_exp_uvars e)
in (let e0 = e
in (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_delayed (_) -> begin
(encode_exp (Microsoft_FStar_Absyn_Util.compress_exp e) env)
end
| Microsoft_FStar_Absyn_Syntax.Exp_bvar (x) -> begin
(let t = (lookup_term_var env x)
in (t, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((v, _)) -> begin
((lookup_free_var env v), [])
end
| Microsoft_FStar_Absyn_Syntax.Exp_constant (c) -> begin
((encode_const c), [])
end
| Microsoft_FStar_Absyn_Syntax.Exp_ascribed ((e, t)) -> begin
(let _45_948 = (e.Microsoft_FStar_Absyn_Syntax.tk := Some (t))
in (encode_exp e env))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (Microsoft_FStar_Absyn_Syntax.Meta_desugared ((e, _))) -> begin
(encode_exp e env)
end
| Microsoft_FStar_Absyn_Syntax.Exp_uvar ((uv, _)) -> begin
(let e = (Microsoft_FStar_ToSMT_Term.mk_Exp_uvar (Support.Microsoft.FStar.Unionfind.uvar_id uv))
in (e, []))
end
| Microsoft_FStar_Absyn_Syntax.Exp_abs ((bs, body)) -> begin
(let fallback = (fun _45_967 -> (match (_45_967) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((f, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in ((Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort)), (decl)::[])))
end))
in (match ((! (e.Microsoft_FStar_Absyn_Syntax.tk))) with
| None -> begin
(let _45_971 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
in (fallback ()))
end
| Some (tfun) -> begin
if (not ((Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function tfun))) then begin
(fallback ())
end else begin
(let tfun = (Microsoft_FStar_Absyn_Util.compress_typ (whnf env tfun))
in (match (tfun.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((bs', c)) -> begin
(let nformals = (Support.List.length bs')
in if ((nformals < (Support.List.length bs)) && (Microsoft_FStar_Absyn_Util.is_total_comp c)) then begin
(let _45_983 = (Support.Microsoft.FStar.Util.first_N nformals bs)
in (match (_45_983) with
| (bs0, rest) -> begin
(let res_t = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder bs0 bs')) with
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s (Microsoft_FStar_Absyn_Util.comp_result c))
end
| _ -> begin
(failwith "Impossible")
end)
in (let e = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (bs0, (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (res_t)) body.Microsoft_FStar_Absyn_Syntax.pos)) (Some (tfun)) e0.Microsoft_FStar_Absyn_Syntax.pos)
in (encode_exp e env)))
end))
end else begin
(let _45_996 = (encode_binders None bs env)
in (match (_45_996) with
| (vars, guards, envbody, decls, _) -> begin
(let _45_999 = (encode_exp body envbody)
in (match (_45_999) with
| (body, decls') -> begin
(let key_body = (Microsoft_FStar_ToSMT_Term.mkForall ([], vars, (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l guards), body))))
in (let cvars = (Microsoft_FStar_ToSMT_Term.free_variables key_body)
in (let tkey = (Microsoft_FStar_ToSMT_Term.mkForall ([], cvars, key_body))
in (match ((Support.Microsoft.FStar.Util.smap_try_find env.cache tkey.Microsoft_FStar_ToSMT_Term.hash)) with
| Some ((t, _, _)) -> begin
((Microsoft_FStar_ToSMT_Term.mkApp (t, (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars))), [])
end
| None -> begin
(match ((is_eta env vars body)) with
| Some (t) -> begin
(t, [])
end
| None -> begin
(let cvar_sorts = (Support.List.map (Support.Prims.snd) cvars)
in (let fsym = (varops.fresh "Exp_abs")
in (let fdecl = Microsoft_FStar_ToSMT_Term.DeclFun ((fsym, cvar_sorts, Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let f = (Microsoft_FStar_ToSMT_Term.mkApp (fsym, (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV cvars)))
in (let app = (mk_ApplyE f vars)
in (let _45_1021 = (encode_typ_pred' None tfun env f)
in (match (_45_1021) with
| (f_has_t, decls'') -> begin
(let typing_f = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((f)::[], cvars, f_has_t)), Some ((Support.String.strcat fsym " typing"))))
in (let interp_f = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((app)::[], (Support.List.append vars cvars), (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_IsTyped app), (Microsoft_FStar_ToSMT_Term.mkEq (app, body)))))), Some ((Support.String.strcat fsym " interpretation"))))
in (let f_decls = (Support.List.append (Support.List.append (Support.List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (let _45_1025 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (fsym, cvar_sorts, f_decls))
in (f, f_decls)))))
end)))))))
end)
end))))
end))
end))
end)
end
| _ -> begin
(failwith "Impossible")
end))
end
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_fvar ((l, _)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, (Support.Microsoft.FStar.Util.Inl (_), _)::(Support.Microsoft.FStar.Util.Inr (v1), _)::(Support.Microsoft.FStar.Util.Inr (v2), _)::[])) when (Microsoft_FStar_Absyn_Syntax.lid_equals l.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.lexcons_lid) -> begin
(let _45_1064 = (encode_exp v1 env)
in (match (_45_1064) with
| (v1, decls1) -> begin
(let _45_1067 = (encode_exp v2 env)
in (match (_45_1067) with
| (v2, decls2) -> begin
((Microsoft_FStar_ToSMT_Term.mk_LexCons v1 v2), (Support.List.append decls1 decls2))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(encode_exp (whnf_e env e) env)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args_e)) -> begin
(let _45_1090 = (encode_args args_e env)
in (match (_45_1090) with
| (args, decls) -> begin
(let encode_partial_app = (fun ht_opt -> (let _45_1095 = (encode_exp head env)
in (match (_45_1095) with
| (head, decls') -> begin
(let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (Support.List.append decls decls'))
end
| Some ((formals, c)) -> begin
(let _45_1104 = (Support.Microsoft.FStar.Util.first_N (Support.List.length args_e) formals)
in (match (_45_1104) with
| (formals, rest) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.formals_for_actuals formals args_e)
in (let ty = ((Microsoft_FStar_Absyn_Util.subst_typ subst) (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e0.Microsoft_FStar_Absyn_Syntax.pos))
in (let _45_1109 = (encode_typ_pred' None ty env app_tm)
in (match (_45_1109) with
| (has_type, decls'') -> begin
(let cvars = (Microsoft_FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((has_type)::[], cvars, has_type)), None))
in (app_tm, (Support.List.append (Support.List.append (Support.List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun fv -> (let _45_1116 = (lookup_free_var_sym env fv)
in (match (_45_1116) with
| (fname, fuel_args) -> begin
(let tm = (Microsoft_FStar_ToSMT_Term.mkApp' (fname, (Support.List.append fuel_args (Support.List.map (fun _45_11 -> (match (_45_11) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args))))
in (tm, decls))
end)))
in (let head = (Microsoft_FStar_Absyn_Util.compress_exp head)
in (let _45_1123 = if ((Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("186"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "Recomputing type for %s\nFull term is %s\n" (Microsoft_FStar_Absyn_Print.exp_to_string head) (Microsoft_FStar_Absyn_Print.exp_to_string e))
end
in (let head_type = (Microsoft_FStar_Absyn_Util.unrefine (whnf env (Microsoft_FStar_Absyn_Util.unrefine (Microsoft_FStar_Tc_Recheck.recompute_typ head))))
in (let _45_1126 = if ((Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("Encoding"))) then begin
(Support.Microsoft.FStar.Util.fprint3 "Recomputed type of head %s (%s) to be %s\n" (Microsoft_FStar_Absyn_Print.exp_to_string head) (Microsoft_FStar_Absyn_Print.tag_of_exp head) (Microsoft_FStar_Absyn_Print.typ_to_string head_type))
end
in (match ((Microsoft_FStar_Absyn_Util.function_formals head_type)) with
| None -> begin
(failwith (Support.Microsoft.FStar.Util.format3 "(%s) term is %s; head type is %s\n" (Support.Microsoft.FStar.Range.string_of_range e0.Microsoft_FStar_Absyn_Syntax.pos) (Microsoft_FStar_Absyn_Print.exp_to_string e0) (Microsoft_FStar_Absyn_Print.typ_to_string head_type)))
end
| Some ((formals, c)) -> begin
(match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_fvar ((fv, _)) when ((Support.List.length formals) = (Support.List.length args)) -> begin
(encode_full_app fv)
end
| _ -> begin
if ((Support.List.length formals) > (Support.List.length args)) then begin
(encode_partial_app (Some ((formals, c))))
end else begin
(encode_partial_app None)
end
end)
end)))))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, (Support.Microsoft.FStar.Util.Inr (_), _, _)::[]), _)) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (((false, (Support.Microsoft.FStar.Util.Inl (x), t1, e1)::[]), e2)) -> begin
(let _45_1168 = (encode_exp e1 env)
in (match (_45_1168) with
| (ee1, decls1) -> begin
(let env' = (push_term_var env x ee1)
in (let _45_1172 = (encode_exp e2 env')
in (match (_45_1172) with
| (ee2, decls2) -> begin
(ee2, (Support.List.append decls1 decls2))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (_) -> begin
(let _45_1176 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (let e = (varops.fresh "let-rec")
in (let decl_e = Microsoft_FStar_ToSMT_Term.DeclFun ((e, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in ((Microsoft_FStar_ToSMT_Term.mkFreeV (e, Microsoft_FStar_ToSMT_Term.Term_sort)), (decl_e)::[]))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(let _45_1186 = (encode_exp e env)
in (match (_45_1186) with
| (scr, decls) -> begin
(let _45_1226 = (Support.List.fold_right (fun _45_1190 _45_1193 -> (match ((_45_1190, _45_1193)) with
| ((p, w, br), (else_case, decls)) -> begin
(let patterns = (encode_pat env p)
in (Support.List.fold_right (fun _45_1197 _45_1200 -> (match ((_45_1197, _45_1200)) with
| ((env0, pattern), (else_case, decls)) -> begin
(let guard = (pattern.guard scr)
in (let projections = (pattern.projections scr)
in (let env = ((Support.List.fold_left (fun env _45_1206 -> (match (_45_1206) with
| (x, t) -> begin
(match (x) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v t)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(push_term_var env x.Microsoft_FStar_Absyn_Syntax.v t)
end)
end)) env) projections)
in (let _45_1220 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(let _45_1217 = (encode_exp w env)
in (match (_45_1217) with
| (w, decls2) -> begin
((Microsoft_FStar_ToSMT_Term.mkAnd (guard, (Microsoft_FStar_ToSMT_Term.mkEq (w, (Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkTrue))))), decls2)
end))
end)
in (match (_45_1220) with
| (guard, decls2) -> begin
(let _45_1223 = (encode_exp br env)
in (match (_45_1223) with
| (br, decls3) -> begin
((Microsoft_FStar_ToSMT_Term.mkITE (guard, br, else_case)), (Support.List.append (Support.List.append decls decls2) decls3))
end))
end)))))
end)) patterns (else_case, decls)))
end)) pats (Microsoft_FStar_ToSMT_Term.mk_Term_unit, decls))
in (match (_45_1226) with
| (match_tm, decls) -> begin
(match_tm, decls)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_meta (_) -> begin
(failwith (Support.Microsoft.FStar.Util.format2 "(%s): Impossible: encode_exp got %s" (Support.Microsoft.FStar.Range.string_of_range e.Microsoft_FStar_Absyn_Syntax.pos) (Microsoft_FStar_Absyn_Print.exp_to_string e)))
end))))
and encode_pat = (fun env pat -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (ps) -> begin
(Support.List.map (encode_one_pat env) ps)
end
| _ -> begin
((encode_one_pat env pat))::[]
end))
and encode_one_pat = (fun env pat -> (let _45_1238 = if (Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint1 "Encoding pattern %s\n" (Microsoft_FStar_Absyn_Print.pat_to_string pat))
end
in (let _45_1242 = (Microsoft_FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_45_1242) with
| (vars, pat_exp_or_typ) -> begin
(let _45_1263 = ((Support.List.fold_left (fun _45_1245 v -> (match (_45_1245) with
| (env, vars) -> begin
(match (v) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _45_1253 = (gen_typ_var env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_45_1253) with
| (aa, _, env) -> begin
(env, ((v, (aa, Microsoft_FStar_ToSMT_Term.Type_sort)))::vars)
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _45_1260 = (gen_term_var env x.Microsoft_FStar_Absyn_Syntax.v)
in (match (_45_1260) with
| (xx, _, env) -> begin
(env, ((v, (xx, Microsoft_FStar_ToSMT_Term.Term_sort)))::vars)
end))
end)
end)) (env, [])) vars)
in (match (_45_1263) with
| (env, vars) -> begin
(let rec mk_guard = (fun pat scrutinee -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_) -> begin
(failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Pat_var (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_term (_)) | (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ (_)) -> begin
Microsoft_FStar_ToSMT_Term.mkTrue
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (c) -> begin
(Microsoft_FStar_ToSMT_Term.mkEq (scrutinee, (encode_const c)))
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, args)) -> begin
(let is_f = (mk_data_tester env f.Microsoft_FStar_Absyn_Syntax.v scrutinee)
in (let sub_term_guards = ((Support.List.mapi (fun i arg -> (let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (mk_guard arg (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[])))))) args)
in (Microsoft_FStar_ToSMT_Term.mk_and_l ((is_f)::sub_term_guards))))
end))
in (let rec mk_projections = (fun pat scrutinee -> (match (pat.Microsoft_FStar_Absyn_Syntax.v) with
| Microsoft_FStar_Absyn_Syntax.Pat_disj (_) -> begin
(failwith "Impossible")
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_term ((x, _))) | (Microsoft_FStar_Absyn_Syntax.Pat_var ((x, _))) | (Microsoft_FStar_Absyn_Syntax.Pat_wild (x)) -> begin
((Support.Microsoft.FStar.Util.Inr (x), scrutinee))::[]
end
| (Microsoft_FStar_Absyn_Syntax.Pat_dot_typ ((a, _))) | (Microsoft_FStar_Absyn_Syntax.Pat_tvar (a)) | (Microsoft_FStar_Absyn_Syntax.Pat_twild (a)) -> begin
((Support.Microsoft.FStar.Util.Inl (a), scrutinee))::[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_constant (_) -> begin
[]
end
| Microsoft_FStar_Absyn_Syntax.Pat_cons ((f, args)) -> begin
((Support.List.flatten) ((Support.List.mapi (fun i arg -> (let proj = (primitive_projector_by_pos env.tcenv f.Microsoft_FStar_Absyn_Syntax.v i)
in (mk_projections arg (Microsoft_FStar_ToSMT_Term.mkApp (proj, (scrutinee)::[])))))) args))
end))
in (let pat_term = (fun _45_1333 -> (match (_45_1333) with
| () -> begin
(match (pat_exp_or_typ) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(encode_typ_term t env)
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(encode_exp e env)
end)
end))
in (let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in (env, pattern)))))
end))
end))))
and encode_args = (fun l env -> (let _45_1363 = ((Support.List.fold_left (fun _45_1343 x -> (match (_45_1343) with
| (tms, decls) -> begin
(match (x) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(let _45_1352 = (encode_typ_term t env)
in (match (_45_1352) with
| (t, decls') -> begin
((Support.Microsoft.FStar.Util.Inl (t))::tms, (Support.List.append decls decls'))
end))
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(let _45_1360 = (encode_exp e env)
in (match (_45_1360) with
| (t, decls') -> begin
((Support.Microsoft.FStar.Util.Inr (t))::tms, (Support.List.append decls decls'))
end))
end)
end)) ([], [])) l)
in (match (_45_1363) with
| (l, decls) -> begin
((Support.List.rev l), decls)
end)))
and encode_formula = (fun phi env -> (let _45_1369 = (encode_formula_with_labels phi env)
in (match (_45_1369) with
| (t, vars, decls) -> begin
(match (vars) with
| [] -> begin
(t, decls)
end
| _ -> begin
(failwith "Unexpected labels in formula")
end)
end)))
and encode_function_type_as_formula = (fun induction_on t env -> (let v_or_t_pat = (fun p -> (match ((Microsoft_FStar_Absyn_Util.unmeta_exp p).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_, (Support.Microsoft.FStar.Util.Inl (_), _)::(Support.Microsoft.FStar.Util.Inr (e), _)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.varg e)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_, (Support.Microsoft.FStar.Util.Inl (t), _)::[])) -> begin
(Microsoft_FStar_Absyn_Syntax.targ t)
end
| _ -> begin
(failwith "Unexpected pattern term")
end))
in (let rec lemma_pats = (fun p -> (match ((Microsoft_FStar_Absyn_Util.unmeta_exp p).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Exp_app ((_, _::(Support.Microsoft.FStar.Util.Inr (hd), _)::(Support.Microsoft.FStar.Util.Inr (tl), _)::[])) -> begin
((v_or_t_pat hd))::(lemma_pats tl)
end
| _ -> begin
[]
end))
in (let _45_1465 = (match ((Microsoft_FStar_Absyn_Util.compress_typ t).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Comp (ct); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _})) -> begin
(match (ct.Microsoft_FStar_Absyn_Syntax.effect_args) with
| (Support.Microsoft.FStar.Util.Inl (pre), _)::(Support.Microsoft.FStar.Util.Inl (post), _)::(Support.Microsoft.FStar.Util.Inr (pats), _)::[] -> begin
(binders, pre, post, (lemma_pats pats))
end
| _ -> begin
(failwith "impos")
end)
end
| _ -> begin
(failwith "Impos")
end)
in (match (_45_1465) with
| (binders, pre, post, patterns) -> begin
(let _45_1472 = (encode_binders None binders env)
in (match (_45_1472) with
| (vars, guards, env, decls, _) -> begin
(let _45_1488 = ((Support.List.unzip) ((Support.List.map (fun _45_12 -> (match (_45_12) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(encode_formula t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(encode_exp e (let _45_1484 = env
in {bindings = _45_1484.bindings; depth = _45_1484.depth; tcenv = _45_1484.tcenv; warn = _45_1484.warn; cache = _45_1484.cache; nolabels = _45_1484.nolabels; use_zfuel_name = true}))
end))) patterns))
in (match (_45_1488) with
| (pats, decls') -> begin
(let pats = (match (induction_on) with
| None -> begin
pats
end
| Some (e) -> begin
(match (vars) with
| [] -> begin
pats
end
| l::[] -> begin
((Microsoft_FStar_ToSMT_Term.mk_Precedes (Microsoft_FStar_ToSMT_Term.mkFreeV l) e))::pats
end
| _ -> begin
(let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
((Microsoft_FStar_ToSMT_Term.mk_Precedes tl e))::pats
end
| (x, Microsoft_FStar_ToSMT_Term.Term_sort)::vars -> begin
(aux (Microsoft_FStar_ToSMT_Term.mk_LexCons (Microsoft_FStar_ToSMT_Term.mkFreeV (x, Microsoft_FStar_ToSMT_Term.Term_sort)) tl) vars)
end
| _ -> begin
pats
end))
in (aux (Microsoft_FStar_ToSMT_Term.mkFreeV ("Prims.LexTop", Microsoft_FStar_ToSMT_Term.Term_sort)) vars))
end)
end)
in (let env = (let _45_1509 = env
in {bindings = _45_1509.bindings; depth = _45_1509.depth; tcenv = _45_1509.tcenv; warn = _45_1509.warn; cache = _45_1509.cache; nolabels = true; use_zfuel_name = _45_1509.use_zfuel_name})
in (let _45_1514 = (encode_formula (Microsoft_FStar_Absyn_Util.unmeta_typ pre) env)
in (match (_45_1514) with
| (pre, decls'') -> begin
(let _45_1517 = (encode_formula (Microsoft_FStar_Absyn_Util.unmeta_typ post) env)
in (match (_45_1517) with
| (post, decls''') -> begin
(let decls = (Support.List.append (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'') decls''')
in ((Microsoft_FStar_ToSMT_Term.mkForall (pats, vars, (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l ((pre)::guards)), post)))), decls))
end))
end))))
end))
end))
end)))))
and encode_formula_with_labels = (fun phi env -> (let enc = (fun f l -> (let _45_1538 = (Support.Microsoft.FStar.Util.fold_map (fun decls x -> (match ((Support.Prims.fst x)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _45_1530 = (encode_typ_term t env)
in (match (_45_1530) with
| (t, decls') -> begin
((Support.List.append decls decls'), t)
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _45_1535 = (encode_exp e env)
in (match (_45_1535) with
| (e, decls') -> begin
((Support.List.append decls decls'), e)
end))
end)) [] l)
in (match (_45_1538) with
| (decls, args) -> begin
((f args), [], decls)
end)))
in (let enc_prop_c = (fun f l -> (let _45_1558 = (Support.List.fold_right (fun t _45_1546 -> (match (_45_1546) with
| (phis, labs, decls) -> begin
(match ((Support.Prims.fst t)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _45_1552 = (encode_formula_with_labels t env)
in (match (_45_1552) with
| (phi, labs', decls') -> begin
((phi)::phis, (Support.List.append labs' labs), (Support.List.append decls' decls))
end))
end
| _ -> begin
(failwith "Expected a formula")
end)
end)) l ([], [], []))
in (match (_45_1558) with
| (phis, labs, decls) -> begin
((f phis), labs, decls)
end)))
in (let const_op = (fun f _45_1561 -> (f, [], []))
in (let un_op = (fun f l -> (f (Support.List.hd l)))
in (let bin_op = (fun f _45_13 -> (match (_45_13) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _ -> begin
(failwith "Impossible")
end))
in (let tri_op = (fun f _45_14 -> (match (_45_14) with
| t1::t2::t3::[] -> begin
(f (t1, t2, t3))
end
| _ -> begin
(failwith "Impossible")
end))
in (let eq_op = (fun _45_15 -> (match (_45_15) with
| _::_::e1::e2::[] -> begin
(enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq) l)
end))
in (let mk_imp = (fun _45_16 -> (match (_45_16) with
| (Support.Microsoft.FStar.Util.Inl (lhs), _)::(Support.Microsoft.FStar.Util.Inl (rhs), _)::[] -> begin
(let _45_1608 = (encode_formula_with_labels rhs env)
in (match (_45_1608) with
| (l1, labs1, decls1) -> begin
(match (l1.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.True, _)) -> begin
(l1, labs1, decls1)
end
| _ -> begin
(let _45_1619 = (encode_formula_with_labels lhs env)
in (match (_45_1619) with
| (l2, labs2, decls2) -> begin
((Microsoft_FStar_ToSMT_Term.mkImp (l2, l1)), (Support.List.append labs1 labs2), (Support.List.append decls1 decls2))
end))
end)
end))
end
| _ -> begin
(failwith "impossible")
end))
in (let mk_ite = (fun _45_17 -> (match (_45_17) with
| (Support.Microsoft.FStar.Util.Inl (guard), _)::(Support.Microsoft.FStar.Util.Inl (_then), _)::(Support.Microsoft.FStar.Util.Inl (_else), _)::[] -> begin
(let _45_1643 = (encode_formula_with_labels guard env)
in (match (_45_1643) with
| (g, labs1, decls1) -> begin
(let _45_1647 = (encode_formula_with_labels _then env)
in (match (_45_1647) with
| (t, labs2, decls2) -> begin
(let _45_1651 = (encode_formula_with_labels _else env)
in (match (_45_1651) with
| (e, labs3, decls3) -> begin
(let res = (Microsoft_FStar_ToSMT_Term.mkITE (g, t, e))
in (res, (Support.List.append (Support.List.append labs1 labs2) labs3), (Support.List.append (Support.List.append decls1 decls2) decls3)))
end))
end))
end))
end
| _ -> begin
(failwith "impossible")
end))
in (let unboxInt_l = (fun f l -> (f (Support.List.map Microsoft_FStar_ToSMT_Term.unboxInt l)))
in (let connectives = ((Microsoft_FStar_Absyn_Const.and_lid, (enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkAnd))))::((Microsoft_FStar_Absyn_Const.or_lid, (enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkOr))))::((Microsoft_FStar_Absyn_Const.imp_lid, mk_imp))::((Microsoft_FStar_Absyn_Const.iff_lid, (enc_prop_c (bin_op Microsoft_FStar_ToSMT_Term.mkIff))))::((Microsoft_FStar_Absyn_Const.ite_lid, mk_ite))::((Microsoft_FStar_Absyn_Const.not_lid, (enc_prop_c (un_op Microsoft_FStar_ToSMT_Term.mkNot))))::((Microsoft_FStar_Absyn_Const.eqT_lid, (enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq))))::((Microsoft_FStar_Absyn_Const.eq2_lid, eq_op))::((Microsoft_FStar_Absyn_Const.true_lid, (const_op Microsoft_FStar_ToSMT_Term.mkTrue)))::((Microsoft_FStar_Absyn_Const.false_lid, (const_op Microsoft_FStar_ToSMT_Term.mkFalse)))::[]
in (let fallback = (fun phi -> (match (phi.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_meta (Microsoft_FStar_Absyn_Syntax.Meta_labeled ((phi', msg, r, b))) -> begin
(let _45_1672 = (encode_formula_with_labels phi' env)
in (match (_45_1672) with
| (phi, labs, decls) -> begin
if env.nolabels then begin
(phi, [], decls)
end else begin
(let lvar = ((varops.fresh "label"), Microsoft_FStar_ToSMT_Term.Bool_sort)
in (let lterm = (Microsoft_FStar_ToSMT_Term.mkFreeV lvar)
in (let lphi = (Microsoft_FStar_ToSMT_Term.mkOr (lterm, phi))
in (lphi, ((lvar, msg, r))::labs, decls))))
end
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_const (ih); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _::(Support.Microsoft.FStar.Util.Inr (l), _)::(Support.Microsoft.FStar.Util.Inl (phi), _)::[])) when (Microsoft_FStar_Absyn_Syntax.lid_equals ih.Microsoft_FStar_Absyn_Syntax.v Microsoft_FStar_Absyn_Const.using_IH) -> begin
if (Microsoft_FStar_Absyn_Util.is_lemma phi) then begin
(let _45_1704 = (encode_exp l env)
in (match (_45_1704) with
| (e, decls) -> begin
(let _45_1707 = (encode_function_type_as_formula (Some (e)) phi env)
in (match (_45_1707) with
| (f, decls') -> begin
(f, [], (Support.List.append decls decls'))
end))
end))
end else begin
(Microsoft_FStar_ToSMT_Term.mkTrue, [], [])
end
end
| _ -> begin
(let _45_1712 = (encode_typ_term phi env)
in (match (_45_1712) with
| (tt, decls) -> begin
((Microsoft_FStar_ToSMT_Term.mk_Valid tt), [], decls)
end))
end))
in (let encode_q_body = (fun env bs ps body -> (let _45_1724 = (encode_binders None bs env)
in (match (_45_1724) with
| (vars, guards, env, decls, _) -> begin
(let _45_1740 = ((Support.List.unzip) ((Support.List.map (fun _45_18 -> (match (_45_18) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(encode_formula t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(encode_exp e (let _45_1736 = env
in {bindings = _45_1736.bindings; depth = _45_1736.depth; tcenv = _45_1736.tcenv; warn = _45_1736.warn; cache = _45_1736.cache; nolabels = _45_1736.nolabels; use_zfuel_name = true}))
end))) ps))
in (match (_45_1740) with
| (pats, decls') -> begin
(let _45_1744 = (encode_formula_with_labels body env)
in (match (_45_1744) with
| (body, labs, decls'') -> begin
(vars, pats, (Microsoft_FStar_ToSMT_Term.mk_and_l guards), body, labs, (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls''))
end))
end))
end)))
in (let _45_1745 = if (Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint1 ">>>> Destructing as formula ... %s\n" (Microsoft_FStar_Absyn_Print.formula_to_string phi))
end
in (let phi = (Microsoft_FStar_Absyn_Util.compress_typ phi)
in (match ((Microsoft_FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (Microsoft_FStar_Absyn_Util.BaseConn ((op, arms))) -> begin
(match (((Support.List.tryFind (fun _45_1757 -> (match (_45_1757) with
| (l, _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals op l)
end))) connectives)) with
| None -> begin
(fallback phi)
end
| Some ((_, f)) -> begin
(f arms)
end)
end
| Some (Microsoft_FStar_Absyn_Util.QAll ((vars, pats, body))) -> begin
(let _45_1770 = if (Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint1 ">>>> Got QALL [%s]\n" ((Microsoft_FStar_Absyn_Print.binders_to_string "; ") vars))
end
in (let _45_1778 = (encode_q_body env vars pats body)
in (match (_45_1778) with
| (vars, pats, guard, body, labs, decls) -> begin
((Microsoft_FStar_ToSMT_Term.mkForall (pats, vars, (Microsoft_FStar_ToSMT_Term.mkImp (guard, body)))), labs, decls)
end)))
end
| Some (Microsoft_FStar_Absyn_Util.QEx ((vars, pats, body))) -> begin
(let _45_1791 = (encode_q_body env vars pats body)
in (match (_45_1791) with
| (vars, pats, guard, body, labs, decls) -> begin
((Microsoft_FStar_ToSMT_Term.mkExists (pats, vars, (Microsoft_FStar_ToSMT_Term.mkAnd (guard, body)))), labs, decls)
end))
end)))))))))))))))))

type prims_t =
{mk : Microsoft_FStar_Absyn_Syntax.lident  ->  string  ->  Microsoft_FStar_ToSMT_Term.decl list; is : Microsoft_FStar_Absyn_Syntax.lident  ->  bool}

let prims = (let _45_1797 = (fresh_fvar "a" Microsoft_FStar_ToSMT_Term.Type_sort)
in (match (_45_1797) with
| (asym, a) -> begin
(let _45_1800 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_45_1800) with
| (xsym, x) -> begin
(let _45_1803 = (fresh_fvar "y" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_45_1803) with
| (ysym, y) -> begin
(let deffun = (fun vars body x -> (Microsoft_FStar_ToSMT_Term.DefineFun ((x, vars, Microsoft_FStar_ToSMT_Term.Term_sort, body, None)))::[])
in (let quant = (fun vars body x -> (let t1 = (Microsoft_FStar_ToSMT_Term.mkApp (x, (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)))
in (let vname_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((x, ((Support.List.map (Support.Prims.snd)) vars), Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (vname_decl)::(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((t1)::[], vars, (Microsoft_FStar_ToSMT_Term.mkEq (t1, body)))), None)))::[])))
in (let axy = ((asym, Microsoft_FStar_ToSMT_Term.Type_sort))::((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let prims = ((Microsoft_FStar_Absyn_Const.op_Eq, (quant axy (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkEq (x, y))))))::((Microsoft_FStar_Absyn_Const.op_notEq, (quant axy (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkNot (Microsoft_FStar_ToSMT_Term.mkEq (x, y)))))))::((Microsoft_FStar_Absyn_Const.op_LT, (quant xy (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkLT ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_LTE, (quant xy (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkLTE ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_GT, (quant xy (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkGT ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_GTE, (quant xy (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkGTE ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_Subtraction, (quant xy (Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkSub ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_Minus, (quant qx (Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkMinus (Microsoft_FStar_ToSMT_Term.unboxInt x))))))::((Microsoft_FStar_Absyn_Const.op_Addition, (quant xy (Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkAdd ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_Multiply, (quant xy (Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkMul ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_Division, (quant xy (Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkDiv ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_Modulus, (quant xy (Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkMod ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_And, (quant xy (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkAnd ((Microsoft_FStar_ToSMT_Term.unboxBool x), (Microsoft_FStar_ToSMT_Term.unboxBool y)))))))::((Microsoft_FStar_Absyn_Const.op_Or, (quant xy (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkOr ((Microsoft_FStar_ToSMT_Term.unboxBool x), (Microsoft_FStar_ToSMT_Term.unboxBool y)))))))::((Microsoft_FStar_Absyn_Const.op_Negation, (quant qx (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkNot (Microsoft_FStar_ToSMT_Term.unboxBool x))))))::[]
in (let mk = (fun l v -> ((Support.List.collect (fun _45_1827 -> (match (_45_1827) with
| (_, b) -> begin
(b v)
end))) ((Support.List.filter (fun _45_1823 -> (match (_45_1823) with
| (l', _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l l')
end))) prims)))
in (let is = (fun l -> ((Support.Microsoft.FStar.Util.for_some (fun _45_1833 -> (match (_45_1833) with
| (l', _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l l')
end))) prims))
in {mk = mk; is = is}))))))))
end))
end))
end))

let primitive_type_axioms = (let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let yy = ("y", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let y = (Microsoft_FStar_ToSMT_Term.mkFreeV yy)
in (let mk_unit = (fun _45_1839 tt -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mk_HasType Microsoft_FStar_ToSMT_Term.mk_Term_unit tt), Some ("unit typing"))))::(Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel ((typing_pred)::[], (xx)::[], (Microsoft_FStar_ToSMT_Term.mkImp (typing_pred, (Microsoft_FStar_ToSMT_Term.mkEq (x, Microsoft_FStar_ToSMT_Term.mk_Term_unit)))))), Some ("unit inversion"))))::[]))
in (let mk_bool = (fun _45_1844 tt -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Bool_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel ((typing_pred)::[], (xx)::[], (Microsoft_FStar_ToSMT_Term.mkImp (typing_pred, (Microsoft_FStar_ToSMT_Term.mk_tester "BoxBool" x))))), Some ("bool inversion"))))::(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall (((Microsoft_FStar_ToSMT_Term.boxBool b))::[], (bb)::[], (Microsoft_FStar_ToSMT_Term.mk_HasType (Microsoft_FStar_ToSMT_Term.boxBool b) tt))), Some ("bool typing"))))::[]))))
in (let mk_int = (fun _45_1851 tt -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (Microsoft_FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (Microsoft_FStar_ToSMT_Term.mk_Valid (Microsoft_FStar_ToSMT_Term.mkApp ("Prims.Precedes", (tt)::(tt)::((Microsoft_FStar_ToSMT_Term.boxInt a))::((Microsoft_FStar_ToSMT_Term.boxInt b))::[])))
in (let precedes_y_x = (Microsoft_FStar_ToSMT_Term.mk_Valid (Microsoft_FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[])))
in (Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel ((typing_pred)::[], (xx)::[], (Microsoft_FStar_ToSMT_Term.mkImp (typing_pred, (Microsoft_FStar_ToSMT_Term.mk_tester "BoxInt" x))))), Some ("int inversion"))))::(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall (((Microsoft_FStar_ToSMT_Term.boxInt b))::[], (bb)::[], (Microsoft_FStar_ToSMT_Term.mk_HasType (Microsoft_FStar_ToSMT_Term.boxInt b) tt))), Some ("int typing"))))::(Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel ((typing_pred)::(typing_pred_y)::(precedes_y_x)::[], (xx)::(yy)::[], (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l ((typing_pred)::(typing_pred_y)::((Microsoft_FStar_ToSMT_Term.mkGT ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.mkInteger' 0))))::((Microsoft_FStar_ToSMT_Term.mkGTE ((Microsoft_FStar_ToSMT_Term.unboxInt y), (Microsoft_FStar_ToSMT_Term.mkInteger' 0))))::((Microsoft_FStar_ToSMT_Term.mkLT ((Microsoft_FStar_ToSMT_Term.unboxInt y), (Microsoft_FStar_ToSMT_Term.unboxInt x))))::[])), precedes_y_x)))), Some ("well-founded ordering on nat (alt)"))))::[])))))))))
in (let mk_int_alias = (fun _45_1863 tt -> (Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkEq (tt, (Microsoft_FStar_ToSMT_Term.mkApp (Microsoft_FStar_Absyn_Const.int_lid.Microsoft_FStar_Absyn_Syntax.str, [])))), Some ("mapping to int; for now"))))::[])
in (let mk_str = (fun _45_1867 tt -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.String_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel ((typing_pred)::[], (xx)::[], (Microsoft_FStar_ToSMT_Term.mkImp (typing_pred, (Microsoft_FStar_ToSMT_Term.mk_tester "BoxString" x))))), Some ("string inversion"))))::(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall (((Microsoft_FStar_ToSMT_Term.boxString b))::[], (bb)::[], (Microsoft_FStar_ToSMT_Term.mk_HasType (Microsoft_FStar_ToSMT_Term.boxString b) tt))), Some ("string typing"))))::[]))))
in (let mk_ref = (fun reft_name _45_1875 -> (let r = ("r", Microsoft_FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let refa = (Microsoft_FStar_ToSMT_Term.mkApp (reft_name, ((Microsoft_FStar_ToSMT_Term.mkFreeV aa))::[]))
in (let refb = (Microsoft_FStar_ToSMT_Term.mkApp (reft_name, ((Microsoft_FStar_ToSMT_Term.mkFreeV bb))::[]))
in (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (Microsoft_FStar_ToSMT_Term.mk_HasType x refb)
in (Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel ((typing_pred)::[], (xx)::(aa)::[], (Microsoft_FStar_ToSMT_Term.mkImp (typing_pred, (Microsoft_FStar_ToSMT_Term.mk_tester "BoxRef" x))))), Some ("ref inversion"))))::(Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel' 2 ((typing_pred)::(typing_pred_b)::[], (xx)::(aa)::(bb)::[], (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b)), (Microsoft_FStar_ToSMT_Term.mkEq ((Microsoft_FStar_ToSMT_Term.mkFreeV aa), (Microsoft_FStar_ToSMT_Term.mkFreeV bb))))))), Some ("ref typing is injective"))))::[]))))))))
in (let prims = ((Microsoft_FStar_Absyn_Const.unit_lid, mk_unit))::((Microsoft_FStar_Absyn_Const.bool_lid, mk_bool))::((Microsoft_FStar_Absyn_Const.int_lid, mk_int))::((Microsoft_FStar_Absyn_Const.string_lid, mk_str))::((Microsoft_FStar_Absyn_Const.ref_lid, mk_ref))::((Microsoft_FStar_Absyn_Const.char_lid, mk_int_alias))::((Microsoft_FStar_Absyn_Const.uint8_lid, mk_int_alias))::[]
in (fun t s tt -> (match ((Support.Microsoft.FStar.Util.find_opt (fun _45_1892 -> (match (_45_1892) with
| (l, _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some ((_, f)) -> begin
(f s tt)
end)))))))))))))

let rec encode_sigelt = (fun env se -> (let _45_1901 = if (Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low) then begin
((Support.Microsoft.FStar.Util.fprint1 ">>>>Encoding [%s]\n") (Microsoft_FStar_Absyn_Print.sigelt_to_string se))
end
in (let nm = (match ((Microsoft_FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.Microsoft_FStar_Absyn_Syntax.str
end)
in (let _45_1909 = (encode_sigelt' env se)
in (match (_45_1909) with
| (g, e) -> begin
(match (g) with
| [] -> begin
((Microsoft_FStar_ToSMT_Term.Caption ((Support.Microsoft.FStar.Util.format1 "<Skipped %s/>" nm)))::[], e)
end
| _ -> begin
((Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption ((Support.Microsoft.FStar.Util.format1 "<Start encoding %s>" nm)))::g) ((Microsoft_FStar_ToSMT_Term.Caption ((Support.Microsoft.FStar.Util.format1 "</end encoding %s>" nm)))::[])), e)
end)
end)))))
and encode_sigelt' = (fun env se -> (let should_skip = (fun l -> ((((Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.pure_") || (Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.ex_")) || (Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.st_")) || (Support.Microsoft.FStar.Util.starts_with l.Microsoft_FStar_Absyn_Syntax.str "Prims.all_")))
in (match (se) with
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((_, _, _, _, Microsoft_FStar_Absyn_Syntax.Effect::[], _)) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, _, _, _, _, _)) when (should_skip lid) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, _, _, _, _, _)) when (Microsoft_FStar_Absyn_Syntax.lid_equals lid Microsoft_FStar_Absyn_Const.b2t_lid) -> begin
(let _45_1960 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_45_1960) with
| (tname, ttok, env) -> begin
(let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid_b2t_x = (Microsoft_FStar_ToSMT_Term.mk_Valid (Microsoft_FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[])))
in (let decls = (Microsoft_FStar_ToSMT_Term.DeclFun ((tname, (Microsoft_FStar_ToSMT_Term.Term_sort)::[], Microsoft_FStar_ToSMT_Term.Type_sort, None)))::(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((valid_b2t_x)::[], (xx)::[], (Microsoft_FStar_ToSMT_Term.mkEq (valid_b2t_x, (Microsoft_FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[])))))), Some ("b2t def"))))::[]
in (decls, env)))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, _, t, tags, _)) -> begin
(let _45_1978 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_45_1978) with
| (tname, ttok, env) -> begin
(let _45_1987 = (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((tps', body)) -> begin
((Support.List.append tps tps'), body)
end
| _ -> begin
(tps, t)
end)
in (match (_45_1987) with
| (tps, t) -> begin
(let _45_1994 = (encode_binders None tps env)
in (match (_45_1994) with
| (vars, guards, env', binder_decls, _) -> begin
(let tok_app = (mk_ApplyT (Microsoft_FStar_ToSMT_Term.mkApp (ttok, [])) vars)
in (let tok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in (let app = (Microsoft_FStar_ToSMT_Term.mkApp (tname, (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)))
in (let fresh_tok = (match (vars) with
| [] -> begin
[]
end
| _ -> begin
((Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) (varops.next_id ())))::[]
end)
in (let decls = (Support.List.append (Support.List.append ((Microsoft_FStar_ToSMT_Term.DeclFun ((tname, (Support.List.map (Support.Prims.snd) vars), Microsoft_FStar_ToSMT_Term.Type_sort, None)))::(tok_decl)::[]) fresh_tok) ((Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((tok_app)::[], vars, (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, app)))), Some ("name-token correspondence"))))::[]))
in (let t = (whnf env t)
in (let _45_2012 = if ((Support.Microsoft.FStar.Util.for_some (fun _45_19 -> (match (_45_19) with
| Microsoft_FStar_Absyn_Syntax.Logic -> begin
true
end
| _ -> begin
false
end))) tags) then begin
((Microsoft_FStar_ToSMT_Term.mk_Valid app), (encode_formula t env'))
end else begin
(app, (encode_typ_term t env'))
end
in (match (_45_2012) with
| (def, (body, decls1)) -> begin
(let abbrev_def = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((def)::[], vars, (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l guards), (Microsoft_FStar_ToSMT_Term.mkEq (def, body)))))), Some ("abbrev. elimination")))
in (let kindingAx = (let _45_2016 = (encode_knd (Microsoft_FStar_Tc_Recheck.recompute_kind t) env' app)
in (match (_45_2016) with
| (k, decls) -> begin
(Support.List.append decls ((Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((app)::[], vars, (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l guards), k)))), Some ("abbrev. kinding"))))::[]))
end))
in (let g = (Support.List.append (Support.List.append (Support.List.append binder_decls decls) decls1) ((abbrev_def)::kindingAx))
in (g, env))))
end))))))))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_val_decl ((lid, t, quals, _)) -> begin
(let tt = (whnf env t)
in (let _45_2029 = (encode_free_var env lid t tt quals)
in (match (_45_2029) with
| (decls, env) -> begin
if ((Microsoft_FStar_Absyn_Util.is_smt_lemma t) && (((Support.List.contains Microsoft_FStar_Absyn_Syntax.Assumption) quals) || env.tcenv.Microsoft_FStar_Tc_Env.is_iface)) then begin
((Support.List.append decls (encode_smt_lemma env lid t)), env)
end else begin
(decls, env)
end
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((l, f, _, _)) -> begin
(let _45_2040 = (encode_formula f env)
in (match (_45_2040) with
| (f, decls) -> begin
(let g = (Microsoft_FStar_ToSMT_Term.Assume ((f, Some ((Support.Microsoft.FStar.Util.format1 "Assumption: %s" (Microsoft_FStar_Absyn_Print.sli l))))))::[]
in ((Support.List.append decls g), env))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, tps, k, _, datas, quals, _)) when (Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.precedes_lid) -> begin
(let _45_2056 = (new_typ_constant_and_tok_from_lid env t)
in (match (_45_2056) with
| (tname, ttok, env) -> begin
([], env)
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, _, _, _, _, _, _)) when ((Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.char_lid) || (Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.uint8_lid)) -> begin
(let tname = t.Microsoft_FStar_Absyn_Syntax.str
in (let tsym = (Microsoft_FStar_ToSMT_Term.mkFreeV (tname, Microsoft_FStar_ToSMT_Term.Type_sort))
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((tname, [], Microsoft_FStar_ToSMT_Term.Type_sort, None))
in ((decl)::(primitive_type_axioms t tname tsym), (push_free_tvar env t tname (Some (tsym)))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, tps, k, _, datas, quals, _)) -> begin
(let is_logical = ((Support.Microsoft.FStar.Util.for_some (fun _45_20 -> (match (_45_20) with
| (Microsoft_FStar_Absyn_Syntax.Logic) | (Microsoft_FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _ -> begin
false
end))) quals)
in (let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(let _45_2100 = c
in (match (_45_2100) with
| (name, args, _, _) -> begin
(Microsoft_FStar_ToSMT_Term.DeclFun ((name, ((Support.List.map (Support.Prims.snd)) args), Microsoft_FStar_ToSMT_Term.Type_sort, None)))::[]
end))
end else begin
(Microsoft_FStar_ToSMT_Term.constructor_to_decl c)
end)
in (let inversion_axioms = (fun tapp vars -> if (((Support.List.length datas) = 0) || ((Support.Microsoft.FStar.Util.for_some (fun l -> ((Support.Option.isNone) (Microsoft_FStar_Tc_Env.lookup_qname env.tcenv l)))) datas)) then begin
[]
end else begin
(let _45_2107 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_45_2107) with
| (xxsym, xx) -> begin
(let _45_2150 = ((Support.List.fold_left (fun _45_2110 l -> (match (_45_2110) with
| (out, decls) -> begin
(let data_t = (Microsoft_FStar_Tc_Env.lookup_datacon env.tcenv l)
in (let _45_2120 = (match ((Microsoft_FStar_Absyn_Util.function_formals data_t)) with
| Some ((formals, res)) -> begin
(formals, (Microsoft_FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_45_2120) with
| (args, res) -> begin
(let indices = (match ((Microsoft_FStar_Absyn_Util.compress_typ res).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_app ((_, indices)) -> begin
indices
end
| _ -> begin
[]
end)
in (let env = ((Support.List.fold_left (fun env a -> (match ((Support.Prims.fst a)) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v (Microsoft_FStar_ToSMT_Term.mkApp ((mk_typ_projector_name l a.Microsoft_FStar_Absyn_Syntax.v), (xx)::[])))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(push_term_var env x.Microsoft_FStar_Absyn_Syntax.v (Microsoft_FStar_ToSMT_Term.mkApp ((mk_term_projector_name l x.Microsoft_FStar_Absyn_Syntax.v), (xx)::[])))
end)) env) args)
in (let _45_2138 = (encode_args indices env)
in (match (_45_2138) with
| (indices, decls') -> begin
(let _45_2139 = if ((Support.List.length indices) <> (Support.List.length vars)) then begin
(failwith "Impossible")
end
in (let eqs = (Microsoft_FStar_ToSMT_Term.mk_and_l (Support.List.map2 (fun v a -> (match (a) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(Microsoft_FStar_ToSMT_Term.mkEq ((Microsoft_FStar_ToSMT_Term.mkFreeV v), a))
end
| Support.Microsoft.FStar.Util.Inr (a) -> begin
(Microsoft_FStar_ToSMT_Term.mkEq ((Microsoft_FStar_ToSMT_Term.mkFreeV v), a))
end)) vars indices))
in ((Microsoft_FStar_ToSMT_Term.mkOr (out, (Microsoft_FStar_ToSMT_Term.mkAnd ((mk_data_tester env l xx), eqs)))), (Support.List.append decls decls'))))
end))))
end)))
end)) (Microsoft_FStar_ToSMT_Term.mkFalse, [])) datas)
in (match (_45_2150) with
| (data_ax, decls) -> begin
(let _45_2153 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_45_2153) with
| (ffsym, ff) -> begin
(let xx_has_type = (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[])) xx tapp)
in (Support.List.append decls ((Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((xx_has_type)::[], (add_fuel (ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort) (((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::vars)), (Microsoft_FStar_ToSMT_Term.mkImp (xx_has_type, data_ax)))), Some ("inversion axiom"))))::[])))
end))
end))
end))
end)
in (let k = (Microsoft_FStar_Absyn_Util.close_kind tps k)
in (let _45_2165 = (match ((Microsoft_FStar_Absyn_Util.compress_kind k).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, res)) -> begin
(true, bs, res)
end
| _ -> begin
(false, [], k)
end)
in (match (_45_2165) with
| (is_kind_arrow, formals, res) -> begin
(let _45_2172 = (encode_binders None formals env)
in (match (_45_2172) with
| (vars, guards, env', binder_decls, _) -> begin
(let projection_axioms = (fun tapp vars -> (match (((Support.Microsoft.FStar.Util.find_opt (fun _45_21 -> (match (_45_21) with
| Microsoft_FStar_Absyn_Syntax.Projector (_) -> begin
true
end
| _ -> begin
false
end))) quals)) with
| Some (Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inl (a)))) -> begin
(let rec projectee = (fun i _45_22 -> (match (_45_22) with
| [] -> begin
i
end
| f::tl -> begin
(match ((Support.Prims.fst f)) with
| Support.Microsoft.FStar.Util.Inl (_) -> begin
(projectee (i + 1) tl)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
if (x.Microsoft_FStar_Absyn_Syntax.v.Microsoft_FStar_Absyn_Syntax.ppname.Microsoft_FStar_Absyn_Syntax.idText = "projectee") then begin
i
end else begin
(projectee (i + 1) tl)
end
end)
end))
in (let projectee_pos = (projectee 0 formals)
in (let _45_2211 = (match ((Support.Microsoft.FStar.Util.first_N projectee_pos vars)) with
| (_, xx::suffix) -> begin
(xx, suffix)
end
| _ -> begin
(failwith "impossible")
end)
in (match (_45_2211) with
| (xx, suffix) -> begin
(let dproj_app = (mk_ApplyT (Microsoft_FStar_ToSMT_Term.mkApp ((mk_typ_projector_name d a), ((Microsoft_FStar_ToSMT_Term.mkFreeV xx))::[])) suffix)
in (Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((tapp)::[], vars, (Microsoft_FStar_ToSMT_Term.mkEq (tapp, dproj_app)))), Some ("projector axiom"))))::[])
end))))
end
| _ -> begin
[]
end))
in (let _45_2218 = (new_typ_constant_and_tok_from_lid env t)
in (match (_45_2218) with
| (tname, ttok, env) -> begin
(let ttok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (Microsoft_FStar_ToSMT_Term.mkApp (tname, (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)))
in (let _45_2243 = (let tname_decl = (constructor_or_logic_type_decl (tname, ((Support.List.map (fun _45_2224 -> (match (_45_2224) with
| (n, s) -> begin
((Support.String.strcat tname n), s)
end))) vars), Microsoft_FStar_ToSMT_Term.Type_sort, (varops.next_id ())))
in (let _45_2240 = (match (vars) with
| [] -> begin
([], (push_free_tvar env t tname ((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_ToSMT_Term.mkApp (tname, [])))))
end
| _ -> begin
(let ttok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) (varops.next_id ()))
in (let ttok_app = (mk_ApplyT ttok_tm vars)
in (let pats = if ((not (is_logical)) && ((Support.Microsoft.FStar.Util.for_some (fun _45_23 -> (match (_45_23) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _ -> begin
false
end))) quals)) then begin
((ttok_app)::[])::((tapp)::[])::[]
end else begin
((ttok_app)::[])::[]
end
in (let name_tok_corr = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall' (pats, None, vars, (Microsoft_FStar_ToSMT_Term.mkEq (ttok_app, tapp)))), Some ("name-token correspondence")))
in ((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[], env))))))
end)
in (match (_45_2240) with
| (tok_decls, env) -> begin
((Support.List.append tname_decl tok_decls), env)
end)))
in (match (_45_2243) with
| (decls, env) -> begin
(let kindingAx = (let _45_2246 = (encode_knd res env' tapp)
in (match (_45_2246) with
| (k, decls) -> begin
(let karr = if is_kind_arrow then begin
(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mk_tester "Kind_arrow" (Microsoft_FStar_ToSMT_Term.mk_PreKind ttok_tm)), Some ("kinding"))))::[]
end else begin
[]
end
in (Support.List.append (Support.List.append decls karr) ((Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((tapp)::[], vars, (Microsoft_FStar_ToSMT_Term.mkImp (guard, k)))), Some ("kinding"))))::[])))
end))
in (let aux = if is_logical then begin
(Support.List.append kindingAx (projection_axioms tapp vars))
end else begin
(Support.List.append (Support.List.append (Support.List.append kindingAx (primitive_type_axioms t tname tapp)) (inversion_axioms tapp vars)) (projection_axioms tapp vars))
end
in (let g = (Support.List.append (Support.List.append decls binder_decls) aux)
in (g, env))))
end)))))
end)))
end))
end))))))
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((d, _, _, _, _, _)) when (Microsoft_FStar_Absyn_Syntax.lid_equals d Microsoft_FStar_Absyn_Const.lexcons_lid) -> begin
([], env)
end
| Microsoft_FStar_Absyn_Syntax.Sig_datacon ((d, t, _, quals, _, drange)) -> begin
(let _45_2277 = (new_term_constant_and_tok_from_lid env d)
in (match (_45_2277) with
| (ddconstrsym, ddtok, env) -> begin
(let ddtok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ddtok, []))
in (let _45_2286 = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((f, c)) -> begin
(f, (Microsoft_FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_45_2286) with
| (formals, t_res) -> begin
(let _45_2289 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_45_2289) with
| (fuel_var, fuel_tm) -> begin
(let s_fuel_tm = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (let _45_2296 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_45_2296) with
| (vars, guards, env', binder_decls, names) -> begin
(let projectors = ((Support.List.map (fun _45_24 -> (match (_45_24) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
((mk_typ_projector_name d a), Microsoft_FStar_ToSMT_Term.Type_sort)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
((mk_term_projector_name d x), Microsoft_FStar_ToSMT_Term.Term_sort)
end))) names)
in (let datacons = (Microsoft_FStar_ToSMT_Term.constructor_to_decl (ddconstrsym, projectors, Microsoft_FStar_ToSMT_Term.Term_sort, (varops.next_id ())))
in (let app = (mk_ApplyE ddtok_tm vars)
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let _45_2310 = (encode_typ_pred' None t env ddtok_tm)
in (match (_45_2310) with
| (tok_typing, decls3) -> begin
(let _45_2317 = (encode_binders (Some (s_fuel_tm)) formals env)
in (match (_45_2317) with
| (vars', guards', env'', decls_formals, _) -> begin
(let _45_2322 = (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars')
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred' (Some (fuel_tm)) t_res env'' dapp)))
in (match (_45_2322) with
| (ty_pred', decls_pred) -> begin
(let guard' = (Microsoft_FStar_ToSMT_Term.mk_and_l guards')
in (let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _ -> begin
((Microsoft_FStar_ToSMT_Term.fresh_token (ddtok, Microsoft_FStar_ToSMT_Term.Term_sort) (varops.next_id ())))::[]
end)
in (let encode_elim = (fun _45_2329 -> (match (_45_2329) with
| () -> begin
(let _45_2332 = (Microsoft_FStar_Absyn_Util.head_and_args t_res)
in (match (_45_2332) with
| (head, args) -> begin
(match ((Microsoft_FStar_Absyn_Util.compress_typ head).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _45_2338 = (encode_args args env')
in (match (_45_2338) with
| (encoded_args, arg_decls) -> begin
(let _45_2362 = (Support.List.fold_left (fun _45_2342 arg -> (match (_45_2342) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| Support.Microsoft.FStar.Util.Inl (targ) -> begin
(let _45_2350 = (gen_typ_var env (Microsoft_FStar_Absyn_Util.new_bvd None))
in (match (_45_2350) with
| (_, tv, env) -> begin
(env, (tv)::arg_vars, ((Microsoft_FStar_ToSMT_Term.mkEq (targ, tv)))::eqns)
end))
end
| Support.Microsoft.FStar.Util.Inr (varg) -> begin
(let _45_2357 = (gen_term_var env (Microsoft_FStar_Absyn_Util.new_bvd None))
in (match (_45_2357) with
| (_, xv, env) -> begin
(env, (xv)::arg_vars, ((Microsoft_FStar_ToSMT_Term.mkEq (varg, xv)))::eqns)
end))
end)
end)) (env', [], []) encoded_args)
in (match (_45_2362) with
| (_, arg_vars, eqns) -> begin
(let arg_vars = (Support.List.rev arg_vars)
in (let ty = (Microsoft_FStar_ToSMT_Term.mkApp (encoded_head, arg_vars))
in (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (let ty_pred = (Microsoft_FStar_ToSMT_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (let arg_binders = (Support.List.map Microsoft_FStar_ToSMT_Term.fv_of_term arg_vars)
in (let typing_inversion = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((ty_pred)::[], (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders)), (Microsoft_FStar_ToSMT_Term.mkImp (ty_pred, (Microsoft_FStar_ToSMT_Term.mk_and_l (Support.List.append eqns guards)))))), Some ("data constructor typing elim")))
in (let subterm_ordering = if (Microsoft_FStar_Absyn_Syntax.lid_equals d Microsoft_FStar_Absyn_Const.lextop_lid) then begin
(let x = ((varops.fresh "x"), Microsoft_FStar_ToSMT_Term.Term_sort)
in (let xtm = (Microsoft_FStar_ToSMT_Term.mkFreeV x)
in Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall (((Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp))::[], (x)::[], (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_tester "LexCons" xtm), (Microsoft_FStar_ToSMT_Term.mk_Precedes xtm dapp))))), Some ("lextop is top")))))
end else begin
(let prec = ((Support.List.collect (fun v -> (match ((Support.Prims.snd v)) with
| (Microsoft_FStar_ToSMT_Term.Type_sort) | (Microsoft_FStar_ToSMT_Term.Fuel_sort) -> begin
[]
end
| Microsoft_FStar_ToSMT_Term.Term_sort -> begin
((Microsoft_FStar_ToSMT_Term.mk_Precedes (Microsoft_FStar_ToSMT_Term.mkFreeV v) dapp))::[]
end
| _ -> begin
(failwith "unexpected sort")
end))) vars)
in Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((ty_pred)::[], (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) (Support.List.append vars arg_binders)), (Microsoft_FStar_ToSMT_Term.mkImp (ty_pred, (Microsoft_FStar_ToSMT_Term.mk_and_l prec))))), Some ("subterm ordering"))))
end
in (arg_decls, (typing_inversion)::(subterm_ordering)::[])))))))))
end))
end)))
end
| _ -> begin
(let _45_2382 = (Microsoft_FStar_Tc_Errors.warn drange (Support.Microsoft.FStar.Util.format2 "Constructor %s builds an unexpected type %s\n" (Microsoft_FStar_Absyn_Print.sli d) (Microsoft_FStar_Absyn_Print.typ_to_string head)))
in ([], []))
end)
end))
end))
in (let _45_2386 = (encode_elim ())
in (match (_45_2386) with
| (decls2, elim) -> begin
(let g = (Support.List.append (Support.List.append (Support.List.append (Support.List.append (Support.List.append (Support.List.append (Support.List.append (Support.List.append binder_decls decls2) decls3) ((Microsoft_FStar_ToSMT_Term.DeclFun ((ddtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, Some ((Support.Microsoft.FStar.Util.format1 "data constructor proxy: %s" (Microsoft_FStar_Absyn_Print.sli d))))))::[])) proxy_fresh) decls_formals) decls_pred) ((Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("typing for data constructor proxy"))))::(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((app)::[], vars, (Microsoft_FStar_ToSMT_Term.mkEq (app, dapp)))), Some ("equality for proxy"))))::(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((ty_pred')::[], (add_fuel (fuel_var, Microsoft_FStar_ToSMT_Term.Fuel_sort) vars'), (Microsoft_FStar_ToSMT_Term.mkImp (guard', ty_pred')))), Some ("data constructor typing intro"))))::[])) elim)
in ((Support.List.append datacons g), env))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_bundle ((ses, _, _, _)) -> begin
(let _45_2399 = (encode_signature env ses)
in (match (_45_2399) with
| (g, env) -> begin
(let _45_2411 = ((Support.List.partition (fun _45_25 -> (match (_45_25) with
| Microsoft_FStar_ToSMT_Term.Assume ((_, Some ("inversion axiom"))) -> begin
false
end
| _ -> begin
true
end))) g)
in (match (_45_2411) with
| (g', inversions) -> begin
((Support.List.append g' inversions), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (((is_rec, bindings), _, _, quals)) -> begin
(let eta_expand = (fun binders formals body t -> (let nbinders = (Support.List.length binders)
in (let _45_2430 = (Support.Microsoft.FStar.Util.first_N nbinders formals)
in (match (_45_2430) with
| (formals, extra_formals) -> begin
(let subst = (Support.List.map2 (fun formal binder -> (match (((Support.Prims.fst formal), (Support.Prims.fst binder))) with
| (Support.Microsoft.FStar.Util.Inl (a), Support.Microsoft.FStar.Util.Inl (b)) -> begin
Support.Microsoft.FStar.Util.Inl ((a.Microsoft_FStar_Absyn_Syntax.v, (Microsoft_FStar_Absyn_Util.btvar_to_typ b)))
end
| (Support.Microsoft.FStar.Util.Inr (x), Support.Microsoft.FStar.Util.Inr (y)) -> begin
Support.Microsoft.FStar.Util.Inr ((x.Microsoft_FStar_Absyn_Syntax.v, (Microsoft_FStar_Absyn_Util.bvar_to_exp y)))
end
| _ -> begin
(failwith "Impossible")
end)) formals binders)
in (let extra_formals = (Microsoft_FStar_Absyn_Util.name_binders (Microsoft_FStar_Absyn_Util.subst_binders subst extra_formals))
in (let body = (Microsoft_FStar_Absyn_Syntax.mk_Exp_app_flat (body, ((Support.Prims.snd) (Microsoft_FStar_Absyn_Util.args_of_binders extra_formals))) ((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_Absyn_Util.subst_typ subst t)) body.Microsoft_FStar_Absyn_Syntax.pos)
in ((Support.List.append binders extra_formals), body))))
end))))
in (let destruct_bound_function = (fun flid t_norm e -> (match (e.Microsoft_FStar_Absyn_Syntax.n) with
| (Microsoft_FStar_Absyn_Syntax.Exp_ascribed (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs ((binders, body)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _))) | (Microsoft_FStar_Absyn_Syntax.Exp_abs ((binders, body))) -> begin
(match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((formals, c)) -> begin
(let nformals = (Support.List.length formals)
in (let nbinders = (Support.List.length binders)
in (let tres = (Microsoft_FStar_Absyn_Util.comp_result c)
in if ((nformals < nbinders) && (Microsoft_FStar_Absyn_Util.is_total_comp c)) then begin
(let _45_2480 = (Support.Microsoft.FStar.Util.first_N nformals binders)
in (match (_45_2480) with
| (bs0, rest) -> begin
(let tres = (match ((Microsoft_FStar_Absyn_Util.mk_subst_binder bs0 formals)) with
| Some (s) -> begin
(Microsoft_FStar_Absyn_Util.subst_typ s tres)
end
| _ -> begin
(failwith "impossible")
end)
in (let body = (Microsoft_FStar_Absyn_Syntax.mk_Exp_abs (rest, body) (Some (tres)) body.Microsoft_FStar_Absyn_Syntax.pos)
in (bs0, body, bs0, tres)))
end))
end else begin
if (nformals > nbinders) then begin
(let _45_2489 = (eta_expand binders formals body tres)
in (match (_45_2489) with
| (binders, body) -> begin
(binders, body, formals, tres)
end))
end else begin
(binders, body, formals, tres)
end
end)))
end
| _ -> begin
(failwith (Support.Microsoft.FStar.Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.Microsoft_FStar_Absyn_Syntax.str (Microsoft_FStar_Absyn_Print.exp_to_string e) (Microsoft_FStar_Absyn_Print.typ_to_string t_norm)))
end)
end
| _ -> begin
(match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((formals, c)) -> begin
(let tres = (Microsoft_FStar_Absyn_Util.comp_result c)
in (let _45_2501 = (eta_expand [] formals e tres)
in (match (_45_2501) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _ -> begin
([], e, [], t_norm)
end)
end))
in (Support.Prims.try_with (fun _45_2505 -> (match (_45_2505) with
| () -> begin
if ((Support.Microsoft.FStar.Util.for_some (fun _45_26 -> (match (_45_26) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _ -> begin
false
end))) quals) then begin
([], env)
end else begin
if ((Support.Microsoft.FStar.Util.for_some (fun _45_2527 -> (match (_45_2527) with
| (_, t, _) -> begin
(Microsoft_FStar_Absyn_Util.is_smt_lemma t)
end))) bindings) then begin
(((Support.List.collect (fun _45_2532 -> (match (_45_2532) with
| (flid, t, _) -> begin
if (Microsoft_FStar_Absyn_Util.is_smt_lemma t) then begin
(encode_smt_lemma env (Support.Microsoft.FStar.Util.right flid) t)
end else begin
(raise (Let_rec_unencodeable))
end
end))) bindings), env)
end else begin
(let _45_2554 = ((Support.List.fold_left (fun _45_2537 _45_2542 -> (match ((_45_2537, _45_2542)) with
| ((toks, typs, decls, env), (flid, t, _)) -> begin
(let _45_2543 = if (Microsoft_FStar_Absyn_Util.is_smt_lemma t) then begin
(raise (Let_rec_unencodeable))
end
in (let t_norm = (Microsoft_FStar_Absyn_Util.compress_typ (whnf env t))
in (let _45_2549 = (declare_top_level_let env (Support.Microsoft.FStar.Util.right flid) t t_norm)
in (match (_45_2549) with
| (tok, decl, env) -> begin
((((Support.Microsoft.FStar.Util.right flid), tok))::toks, (t_norm)::typs, (decl)::decls, env)
end))))
end)) ([], [], [], env)) bindings)
in (match (_45_2554) with
| (toks, typs, decls, env) -> begin
(let toks = (Support.List.rev toks)
in (let decls = ((Support.List.flatten) (Support.List.rev decls))
in (let typs = (Support.List.rev typs)
in if (((Support.Microsoft.FStar.Util.for_some (fun _45_27 -> (match (_45_27) with
| Microsoft_FStar_Absyn_Syntax.HasMaskedEffect -> begin
true
end
| _ -> begin
false
end))) quals) || ((Support.Microsoft.FStar.Util.for_some (fun t -> ((Microsoft_FStar_Absyn_Util.is_lemma t) || (not ((Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t)))))) typs)) then begin
(decls, env)
end else begin
if (not (is_rec)) then begin
(match ((bindings, typs, toks)) with
| ((_, _, e)::[], t_norm::[], (flid, (f, ftok))::[]) -> begin
(let _45_2583 = (destruct_bound_function flid t_norm e)
in (match (_45_2583) with
| (binders, body, formals, tres) -> begin
(let _45_2590 = (encode_binders None binders env)
in (match (_45_2590) with
| (vars, guards, env', binder_decls, _) -> begin
(let app = (match (vars) with
| [] -> begin
(Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
end
| _ -> begin
(Microsoft_FStar_ToSMT_Term.mkApp (f, (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)))
end)
in (let _45_2597 = (encode_exp body env')
in (match (_45_2597) with
| (body, decls2) -> begin
(let eqn = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((app)::[], vars, (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l guards), (Microsoft_FStar_ToSMT_Term.mkEq (app, body)))))), Some ((Support.Microsoft.FStar.Util.format1 "Equation for %s" flid.Microsoft_FStar_Absyn_Syntax.str))))
in ((Support.List.append (Support.List.append (Support.List.append decls binder_decls) decls2) ((eqn)::[])), env))
end)))
end))
end))
end
| _ -> begin
(failwith "Impossible")
end)
end else begin
(let fuel = ((varops.fresh "fuel"), Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (let fuel_tm = (Microsoft_FStar_ToSMT_Term.mkFreeV fuel)
in (let env0 = env
in (let _45_2617 = ((Support.List.fold_left (fun _45_2606 _45_2611 -> (match ((_45_2606, _45_2611)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (push_free_var env flid gtok ((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)) toks)
in (match (_45_2617) with
| (gtoks, env) -> begin
(let gtoks = (Support.List.rev gtoks)
in (let encode_one_binding = (fun env0 _45_2626 t_norm _45_2633 -> (match ((_45_2626, _45_2633)) with
| ((flid, f, ftok, g, gtok), (_, _, e)) -> begin
(let _45_2638 = (destruct_bound_function flid t_norm e)
in (match (_45_2638) with
| (binders, body, formals, tres) -> begin
(let _45_2645 = (encode_binders None binders env)
in (match (_45_2645) with
| (vars, guards, env', binder_decls, _) -> begin
(let decl_g = Microsoft_FStar_ToSMT_Term.DeclFun ((g, (Microsoft_FStar_ToSMT_Term.Fuel_sort)::(Support.List.map (Support.Prims.snd) vars), Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = Microsoft_FStar_ToSMT_Term.DeclFun ((gtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let app = (Microsoft_FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (Microsoft_FStar_ToSMT_Term.mkApp (g, ((Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[])))::vars_tm))
in (let gmax = (Microsoft_FStar_ToSMT_Term.mkApp (g, ((Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", [])))::vars_tm))
in (let _45_2655 = (encode_exp body env')
in (match (_45_2655) with
| (body_tm, decls2) -> begin
(let eqn_g = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((gsapp)::[], (fuel)::vars, (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l guards), (Microsoft_FStar_ToSMT_Term.mkEq (gsapp, body_tm)))))), Some ((Support.Microsoft.FStar.Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.Microsoft_FStar_Absyn_Syntax.str))))
in (let eqn_f = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((app)::[], vars, (Microsoft_FStar_ToSMT_Term.mkEq (app, gmax)))), Some ("Correspondence of recursive function to instrumented version")))
in (let eqn_g' = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((gsapp)::[], (fuel)::vars, (Microsoft_FStar_ToSMT_Term.mkEq (gsapp, (Microsoft_FStar_ToSMT_Term.mkApp (g, ((Microsoft_FStar_ToSMT_Term.mkFreeV fuel))::vars_tm)))))), Some ("Fuel irrelevance")))
in (let _45_2678 = (let _45_2665 = (encode_binders None formals env0)
in (match (_45_2665) with
| (vars, v_guards, env, binder_decls, _) -> begin
(let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (mk_ApplyE (Microsoft_FStar_ToSMT_Term.mkFreeV (gtok, Microsoft_FStar_ToSMT_Term.Term_sort)) ((fuel)::vars))
in Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((tok_app)::[], (fuel)::vars, (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, gapp)))), Some ("Fuel token correspondence"))))
in (let _45_2675 = (let _45_2672 = (encode_typ_pred' None tres env gapp)
in (match (_45_2672) with
| (g_typing, d3) -> begin
(d3, (Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((gapp)::[], (fuel)::vars, (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l v_guards), g_typing)))), None)))::[])
end))
in (match (_45_2675) with
| (aux_decls, typing_corr) -> begin
((Support.List.append binder_decls aux_decls), (Support.List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_45_2678) with
| (aux_decls, g_typing) -> begin
((Support.List.append (Support.List.append (Support.List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (Support.List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (let _45_2694 = (Support.List.fold_left (fun _45_2682 _45_2686 -> (match ((_45_2682, _45_2686)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _45_2690 = (encode_one_binding env0 gtok ty bs)
in (match (_45_2690) with
| (decls', eqns', env0) -> begin
((decls')::decls, (Support.List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) (Support.List.zip3 gtoks typs bindings))
in (match (_45_2694) with
| (decls, eqns, env0) -> begin
(let _45_2703 = ((Support.List.partition (fun _45_28 -> (match (_45_28) with
| Microsoft_FStar_ToSMT_Term.DeclFun (_) -> begin
true
end
| _ -> begin
false
end))) ((Support.List.flatten) decls))
in (match (_45_2703) with
| (prefix_decls, rest) -> begin
(let eqns = (Support.List.rev eqns)
in ((Support.List.append (Support.List.append prefix_decls rest) eqns), env0))
end))
end))))
end)))))
end
end)))
end))
end
end
end)) (fun _45_2504 -> (match (_45_2504) with
| Let_rec_unencodeable -> begin
(let msg = ((Support.String.concat " and ") ((Support.List.map (fun _45_2513 -> (match (_45_2513) with
| (lb, _, _) -> begin
(Microsoft_FStar_Absyn_Print.lbname_to_string lb)
end))) bindings))
in (let decl = Microsoft_FStar_ToSMT_Term.Caption ((Support.String.strcat "let rec unencodeable: Skipping: " msg))
in ((decl)::[], env)))
end)))))
end
| (Microsoft_FStar_Absyn_Syntax.Sig_pragma (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_main (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_new_effect (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_effect_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_kind_abbrev (_)) | (Microsoft_FStar_Absyn_Syntax.Sig_sub_effect (_)) -> begin
([], env)
end)))
and declare_top_level_let = (fun env x t t_norm -> (match ((try_lookup_lid env x)) with
| None -> begin
(let _45_2730 = (encode_free_var env x t t_norm [])
in (match (_45_2730) with
| (decls, env) -> begin
(let _45_2735 = (lookup_lid env x)
in (match (_45_2735) with
| (n, x', _) -> begin
((n, x'), decls, env)
end))
end))
end
| Some ((n, x, _)) -> begin
((n, x), [], env)
end))
and encode_smt_lemma = (fun env lid t -> (let _45_2747 = (encode_function_type_as_formula None t env)
in (match (_45_2747) with
| (form, decls) -> begin
(Support.List.append decls ((Microsoft_FStar_ToSMT_Term.Assume ((form, Some ((Support.String.strcat "Lemma: " lid.Microsoft_FStar_Absyn_Syntax.str)))))::[]))
end)))
and encode_free_var = (fun env lid tt t_norm quals -> if ((not ((Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t_norm))) || (Microsoft_FStar_Absyn_Util.is_lemma t_norm)) then begin
(let _45_2756 = (new_term_constant_and_tok_from_lid env lid)
in (match (_45_2756) with
| (vname, vtok, env) -> begin
(let arg_sorts = (match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, _)) -> begin
((Support.List.map (fun _45_29 -> (match (_45_29) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _ -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))) binders)
end
| _ -> begin
[]
end)
in (let d = Microsoft_FStar_ToSMT_Term.DeclFun ((vname, arg_sorts, Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted function symbol for impure function")))
in (let dd = Microsoft_FStar_ToSMT_Term.DeclFun ((vtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Uninterpreted name for impure function")))
in ((d)::(dd)::[], env))))
end))
end else begin
if (prims.is lid) then begin
(let vname = (varops.new_fvar lid)
in (let definition = (prims.mk lid vname)
in (let env = (push_free_var env lid vname None)
in (definition, env))))
end else begin
(let _45_2786 = (match ((Microsoft_FStar_Absyn_Util.function_formals t_norm)) with
| Some ((args, comp)) -> begin
(args, (Microsoft_FStar_Absyn_Util.comp_result comp))
end
| None -> begin
([], t_norm)
end)
in (match (_45_2786) with
| (formals, res) -> begin
(let _45_2790 = (new_term_constant_and_tok_from_lid env lid)
in (match (_45_2790) with
| (vname, vtok, env) -> begin
(let vtok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (vtok, []))
in (let mk_disc_proj_axioms = (fun vapp vars -> ((Support.List.collect (fun _45_30 -> (match (_45_30) with
| Microsoft_FStar_Absyn_Syntax.Discriminator (d) -> begin
(let _45_2804 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_45_2804) with
| (_, (xxsym, _)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((vapp)::[], vars, (Microsoft_FStar_ToSMT_Term.mkEq (vapp, (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mk_tester (escape d.Microsoft_FStar_Absyn_Syntax.str) xx)))))), None)))::[])
end))
end
| Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inr (f))) -> begin
(let _45_2817 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_45_2817) with
| (_, (xxsym, _)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((vapp)::[], vars, (Microsoft_FStar_ToSMT_Term.mkEq (vapp, (Microsoft_FStar_ToSMT_Term.mkApp ((mk_term_projector_name d f), (xx)::[])))))), None)))::[])
end))
end
| _ -> begin
[]
end))) quals))
in (let _45_2827 = (encode_binders None formals env)
in (match (_45_2827) with
| (vars, guards, env', decls1, _) -> begin
(let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (Microsoft_FStar_ToSMT_Term.mkApp (vname, (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)))
in (let _45_2860 = (let vname_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((vname, ((Support.List.map (fun _45_31 -> (match (_45_31) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _ -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))) formals), Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _45_2857 = (match (formals) with
| [] -> begin
(let _45_2844 = if (not ((head_normal env tt))) then begin
(encode_typ_pred' None tt env (Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort)))
end else begin
(encode_typ_pred' None t_norm env (Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort)))
end
in (match (_45_2844) with
| (t, decls2) -> begin
(let tok_typing = Microsoft_FStar_ToSMT_Term.Assume ((t, Some ("function token typing")))
in ((Support.List.append decls2 ((tok_typing)::[])), (push_free_var env lid vname ((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort))))))
end))
end
| _ -> begin
(let vtok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((vtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (Microsoft_FStar_ToSMT_Term.fresh_token (vtok, Microsoft_FStar_ToSMT_Term.Term_sort) (varops.next_id ()))
in (let name_tok_corr = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((vtok_app)::[], vars, (Microsoft_FStar_ToSMT_Term.mkEq (vtok_app, vapp)))), None))
in (let _45_2853 = if (not ((head_normal env tt))) then begin
(encode_typ_pred' None tt env vtok_tm)
end else begin
(encode_typ_pred' None t_norm env vtok_tm)
end
in (match (_45_2853) with
| (tok_typing, decls2) -> begin
(let tok_typing = Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in ((Support.List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))
end)))))
end)
in (match (_45_2857) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
in (match (_45_2860) with
| (decls2, env) -> begin
(let _45_2863 = (encode_typ_pred' None res env' vapp)
in (match (_45_2863) with
| (ty_pred, decls3) -> begin
(let _45_2869 = if (not ((head_normal env tt))) then begin
(let _45_2866 = (encode_typ_pred' None tt env vtok_tm)
in (match (_45_2866) with
| (tok_typing, decls4) -> begin
((Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, None)))::[], decls4)
end))
end else begin
([], [])
end
in (match (_45_2869) with
| (tt_typing, decls4) -> begin
(let typingAx = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((vapp)::[], vars, (Microsoft_FStar_ToSMT_Term.mkImp (guard, ty_pred)))), Some ("free var typing")))
in (let g = (Support.List.append (Support.List.append (Support.List.append (Support.List.append (Support.List.append decls1 decls2) decls3) decls4) ((typingAx)::tt_typing)) (mk_disc_proj_axioms vapp vars))
in (g, env)))
end))
end))
end)))))
end))))
end))
end))
end
end)
and encode_signature = (fun env ses -> ((Support.List.fold_left (fun _45_2876 se -> (match (_45_2876) with
| (g, env) -> begin
(let _45_2880 = (encode_sigelt env se)
in (match (_45_2880) with
| (g', env) -> begin
((Support.List.append g g'), env)
end))
end)) ([], env)) ses))

let encode_env_bindings = (fun env bindings -> (let encode_binding = (fun b _45_2887 -> (match (_45_2887) with
| (decls, env) -> begin
(match (b) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t0)) -> begin
(let _45_2895 = (new_term_constant env x)
in (match (_45_2895) with
| (xxsym, xx, env') -> begin
(let t1 = (Microsoft_FStar_Tc_Normalize.norm_typ ((Microsoft_FStar_Tc_Normalize.DeltaHard)::(Microsoft_FStar_Tc_Normalize.Beta)::(Microsoft_FStar_Tc_Normalize.Eta)::(Microsoft_FStar_Tc_Normalize.Simplify)::[]) env.tcenv t0)
in (let _45_2899 = (encode_typ_pred' None t1 env xx)
in (match (_45_2899) with
| (t, decls') -> begin
(let caption = if (! (Microsoft_FStar_Options.logQueries)) then begin
Some ((Support.Microsoft.FStar.Util.format3 "%s : %s (%s)" (Microsoft_FStar_Absyn_Print.strBvd x) (Microsoft_FStar_Absyn_Print.typ_to_string t0) (Microsoft_FStar_Absyn_Print.typ_to_string t1)))
end else begin
None
end
in (let g = (Support.List.append (Support.List.append ((Microsoft_FStar_ToSMT_Term.DeclFun ((xxsym, [], Microsoft_FStar_ToSMT_Term.Term_sort, caption)))::[]) decls') ((Microsoft_FStar_ToSMT_Term.Assume ((t, None)))::[]))
in ((Support.List.append decls g), env')))
end)))
end))
end
| Microsoft_FStar_Tc_Env.Binding_typ ((a, k)) -> begin
(let _45_2909 = (new_typ_constant env a)
in (match (_45_2909) with
| (aasym, aa, env') -> begin
(let _45_2912 = (encode_knd k env aa)
in (match (_45_2912) with
| (k, decls') -> begin
(let g = (Support.List.append (Support.List.append ((Microsoft_FStar_ToSMT_Term.DeclFun ((aasym, [], Microsoft_FStar_ToSMT_Term.Type_sort, Some ((Microsoft_FStar_Absyn_Print.strBvd a)))))::[]) decls') ((Microsoft_FStar_ToSMT_Term.Assume ((k, None)))::[]))
in ((Support.List.append decls g), env'))
end))
end))
end
| Microsoft_FStar_Tc_Env.Binding_lid ((x, t)) -> begin
(let t_norm = (whnf env t)
in (let _45_2921 = (encode_free_var env x t t_norm [])
in (match (_45_2921) with
| (g, env') -> begin
((Support.List.append decls g), env')
end)))
end
| Microsoft_FStar_Tc_Env.Binding_sig (se) -> begin
(let _45_2926 = (encode_sigelt env se)
in (match (_45_2926) with
| (g, env') -> begin
((Support.List.append decls g), env')
end))
end)
end))
in (Support.List.fold_right encode_binding bindings ([], env))))

let encode_labels = (fun labs -> (let prefix = ((Support.List.map (fun _45_2933 -> (match (_45_2933) with
| (l, _, _) -> begin
Microsoft_FStar_ToSMT_Term.DeclFun (((Support.Prims.fst l), [], Microsoft_FStar_ToSMT_Term.Bool_sort, None))
end))) labs)
in (let suffix = ((Support.List.collect (fun _45_2940 -> (match (_45_2940) with
| (l, _, _) -> begin
(Microsoft_FStar_ToSMT_Term.Echo ((Support.Prims.fst l)))::(Microsoft_FStar_ToSMT_Term.Eval ((Microsoft_FStar_ToSMT_Term.mkFreeV l)))::[]
end))) labs)
in (prefix, suffix))))

let last_env = (Support.Microsoft.FStar.Util.mk_ref [])

let init_env = (fun tcenv -> (last_env := ({bindings = []; depth = 0; tcenv = tcenv; warn = true; cache = (Support.Microsoft.FStar.Util.smap_create 100); nolabels = false; use_zfuel_name = false})::[]))

let get_env = (fun tcenv -> (match ((! (last_env))) with
| [] -> begin
(failwith "No env; call init first!")
end
| e::_ -> begin
(let _45_2949 = e
in {bindings = _45_2949.bindings; depth = _45_2949.depth; tcenv = tcenv; warn = _45_2949.warn; cache = _45_2949.cache; nolabels = _45_2949.nolabels; use_zfuel_name = _45_2949.use_zfuel_name})
end))

let set_env = (fun env -> (match ((! (last_env))) with
| [] -> begin
(failwith "Empty env stack")
end
| _::tl -> begin
(last_env := (env)::tl)
end))

let push_env = (fun _45_2957 -> (match (_45_2957) with
| () -> begin
(match ((! (last_env))) with
| [] -> begin
(failwith "Empty env stack")
end
| hd::tl -> begin
(let _45_2962 = (Microsoft_FStar_ToSMT_Term.push ())
in (let refs = (Support.Microsoft.FStar.Util.smap_copy hd.cache)
in (let top = (let _45_2965 = hd
in {bindings = _45_2965.bindings; depth = _45_2965.depth; tcenv = _45_2965.tcenv; warn = _45_2965.warn; cache = refs; nolabels = _45_2965.nolabels; use_zfuel_name = _45_2965.use_zfuel_name})
in (last_env := (top)::(hd)::tl))))
end)
end))

let pop_env = (fun _45_2968 -> (match (_45_2968) with
| () -> begin
(match ((! (last_env))) with
| [] -> begin
(failwith "Popping an empty stack")
end
| _::tl -> begin
(let _45_2974 = (Microsoft_FStar_ToSMT_Term.pop ())
in (last_env := tl))
end)
end))

let mark_env = (fun _45_2976 -> (match (_45_2976) with
| () -> begin
(push_env ())
end))

let reset_mark_env = (fun _45_2977 -> (match (_45_2977) with
| () -> begin
(pop_env ())
end))

let commit_mark_env = (fun _45_2978 -> (match (_45_2978) with
| () -> begin
(let _45_2979 = (Microsoft_FStar_ToSMT_Term.commit_mark ())
in (match ((! (last_env))) with
| hd::_::tl -> begin
(last_env := (hd)::tl)
end
| _ -> begin
(failwith "Impossible")
end))
end))

let init = (fun tcenv -> (let _45_2990 = (init_env tcenv)
in (let _45_2992 = (Microsoft_FStar_ToSMT_Z3.init ())
in (Microsoft_FStar_ToSMT_Z3.giveZ3 ((Microsoft_FStar_ToSMT_Term.DefPrelude)::[])))))

let push = (fun msg -> (let _45_2995 = (push_env ())
in (let _45_2997 = (varops.push ())
in (Microsoft_FStar_ToSMT_Z3.push msg))))

let pop = (fun msg -> (let _45_3000 = ((Support.Prims.ignore) (pop_env ()))
in (let _45_3002 = (varops.pop ())
in (Microsoft_FStar_ToSMT_Z3.pop msg))))

let mark = (fun msg -> (let _45_3005 = (mark_env ())
in (let _45_3007 = (varops.mark ())
in (Microsoft_FStar_ToSMT_Z3.mark msg))))

let reset_mark = (fun msg -> (let _45_3010 = (reset_mark_env ())
in (let _45_3012 = (varops.reset_mark ())
in (Microsoft_FStar_ToSMT_Z3.reset_mark msg))))

let commit_mark = (fun msg -> (let _45_3015 = (commit_mark_env ())
in (let _45_3017 = (varops.commit_mark ())
in (Microsoft_FStar_ToSMT_Z3.commit_mark msg))))

let encode_sig = (fun tcenv se -> (let caption = (fun decls -> if (! (Microsoft_FStar_Options.logQueries)) then begin
(Microsoft_FStar_ToSMT_Term.Caption ((Support.String.strcat "encoding sigelt " (Microsoft_FStar_Absyn_Print.sigelt_to_string_short se))))::decls
end else begin
decls
end)
in (let env = (get_env tcenv)
in (let _45_3026 = (encode_sigelt env se)
in (match (_45_3026) with
| (decls, env) -> begin
(let _45_3027 = (set_env env)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 (caption decls)))
end)))))

let encode_modul = (fun tcenv modul -> (let name = (Support.Microsoft.FStar.Util.format2 "%s %s" (if modul.Microsoft_FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)
in (let _45_3032 = if (Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint2 "Encoding externals for %s ... %s exports\n" name (Support.Microsoft.FStar.Util.string_of_int (Support.List.length modul.Microsoft_FStar_Absyn_Syntax.exports)))
end
in (let env = (get_env tcenv)
in (let _45_3039 = (encode_signature (let _45_3035 = env
in {bindings = _45_3035.bindings; depth = _45_3035.depth; tcenv = _45_3035.tcenv; warn = false; cache = _45_3035.cache; nolabels = _45_3035.nolabels; use_zfuel_name = _45_3035.use_zfuel_name}) modul.Microsoft_FStar_Absyn_Syntax.exports)
in (match (_45_3039) with
| (decls, env) -> begin
(let caption = (fun decls -> if (! (Microsoft_FStar_Options.logQueries)) then begin
(let msg = (Support.String.strcat "Externals for " name)
in (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::decls) ((Microsoft_FStar_ToSMT_Term.Caption ((Support.String.strcat "End " msg)))::[])))
end else begin
decls
end)
in (let _45_3045 = (set_env (let _45_3043 = env
in {bindings = _45_3043.bindings; depth = _45_3043.depth; tcenv = _45_3043.tcenv; warn = true; cache = _45_3043.cache; nolabels = _45_3043.nolabels; use_zfuel_name = _45_3043.use_zfuel_name}))
in (let _45_3047 = if (Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint1 "Done encoding externals for %s\n" name)
end
in (let decls = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

let solve = (fun tcenv q -> (let _45_3052 = (push (Support.Microsoft.FStar.Util.format1 "Starting query at %s" (Support.Microsoft.FStar.Range.string_of_range (Microsoft_FStar_Tc_Env.get_range tcenv))))
in (let pop = (fun _45_3055 -> (match (_45_3055) with
| () -> begin
(pop (Support.Microsoft.FStar.Util.format1 "Ending query at %s" (Support.Microsoft.FStar.Range.string_of_range (Microsoft_FStar_Tc_Env.get_range tcenv))))
end))
in (let _45_3085 = (let env = (get_env tcenv)
in (let bindings = (Microsoft_FStar_Tc_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (let _45_3068 = (encode_env_bindings env (Support.List.filter (fun _45_32 -> (match (_45_32) with
| Microsoft_FStar_Tc_Env.Binding_sig (_) -> begin
false
end
| _ -> begin
true
end)) bindings))
in (match (_45_3068) with
| (env_decls, env) -> begin
(let _45_3069 = if (Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint1 "Encoding query formula: %s\n" (Microsoft_FStar_Absyn_Print.formula_to_string q))
end
in (let _45_3074 = (encode_formula_with_labels q env)
in (match (_45_3074) with
| (phi, labels, qdecls) -> begin
(let _45_3077 = (encode_labels labels)
in (match (_45_3077) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (Support.List.append (Support.List.append env_decls label_prefix) qdecls)
in (let qry = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkNot phi), Some ("query")))
in (let suffix = (Support.List.append label_suffix ((Microsoft_FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))))
in (match (_45_3085) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| Microsoft_FStar_ToSMT_Term.Assume (({Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.False, _)); Microsoft_FStar_ToSMT_Term.hash = _; Microsoft_FStar_ToSMT_Term.freevars = _}, _)) -> begin
(let _45_3100 = (pop ())
in ())
end
| _ when tcenv.Microsoft_FStar_Tc_Env.admit -> begin
(let _45_3104 = (pop ())
in ())
end
| Microsoft_FStar_ToSMT_Term.Assume ((q, _)) -> begin
(let fresh = ((Support.String.length q.Microsoft_FStar_ToSMT_Term.hash) >= 2048)
in (let _45_3112 = (Microsoft_FStar_ToSMT_Z3.giveZ3 prefix)
in (let with_fuel = (fun p _45_3118 -> (match (_45_3118) with
| (n, i) -> begin
(Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption ((Support.Microsoft.FStar.Util.format1 "<fuel=\'%s\'>" (Support.Microsoft.FStar.Util.string_of_int n))))::(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkEq ((Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", [])), (Microsoft_FStar_ToSMT_Term.n_fuel n))), None)))::(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkEq ((Microsoft_FStar_ToSMT_Term.mkApp ("MaxIFuel", [])), (Microsoft_FStar_ToSMT_Term.n_fuel i))), None)))::(p)::(Microsoft_FStar_ToSMT_Term.CheckSat)::[]) suffix)
end))
in (let check = (fun p -> (let initial_config = ((! (Microsoft_FStar_Options.initial_fuel)), (! (Microsoft_FStar_Options.initial_ifuel)))
in (let alt_configs = (Support.List.flatten ((if ((! (Microsoft_FStar_Options.max_ifuel)) > (! (Microsoft_FStar_Options.initial_ifuel))) then begin
(((! (Microsoft_FStar_Options.initial_fuel)), (! (Microsoft_FStar_Options.max_ifuel))))::[]
end else begin
[]
end)::(if (((! (Microsoft_FStar_Options.max_fuel)) / 2) > (! (Microsoft_FStar_Options.initial_fuel))) then begin
((((! (Microsoft_FStar_Options.max_fuel)) / 2), (! (Microsoft_FStar_Options.max_ifuel))))::[]
end else begin
[]
end)::(if (((! (Microsoft_FStar_Options.max_fuel)) > (! (Microsoft_FStar_Options.initial_fuel))) && ((! (Microsoft_FStar_Options.max_ifuel)) > (! (Microsoft_FStar_Options.initial_ifuel)))) then begin
(((! (Microsoft_FStar_Options.max_fuel)), (! (Microsoft_FStar_Options.max_ifuel))))::[]
end else begin
[]
end)::(if ((! (Microsoft_FStar_Options.min_fuel)) < (! (Microsoft_FStar_Options.initial_fuel))) then begin
(((! (Microsoft_FStar_Options.min_fuel)), 1))::[]
end else begin
[]
end)::[]))
in (let report = (fun _45_3126 -> (match (_45_3126) with
| (ok, errs) -> begin
if ok then begin
()
end else begin
(let errs = (match (errs) with
| [] -> begin
(("Unknown assertion failed", Microsoft_FStar_Absyn_Syntax.dummyRange))::[]
end
| _ -> begin
errs
end)
in (Microsoft_FStar_Tc_Errors.add_errors tcenv errs))
end
end))
in (let rec try_alt_configs = (fun p errs _45_33 -> (match (_45_33) with
| [] -> begin
(report (false, errs))
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(Microsoft_FStar_ToSMT_Z3.ask fresh labels (with_fuel p mi) (cb p []))
end
| _ -> begin
(report (false, errs))
end)
end
| mi::tl -> begin
(Microsoft_FStar_ToSMT_Z3.ask fresh labels (with_fuel p mi) (fun _45_3147 -> (match (_45_3147) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb p tl (ok, errs'))
end
| _ -> begin
(cb p tl (ok, errs))
end)
end)))
end))
and cb = (fun p alt _45_3155 -> (match (_45_3155) with
| (ok, errs) -> begin
if ok then begin
()
end else begin
(try_alt_configs p errs alt)
end
end))
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels (with_fuel p initial_config) (cb p alt_configs)))))))
in (let process_query = (fun q -> if ((! (Microsoft_FStar_Options.split_cases)) > 0) then begin
(let _45_3160 = (Microsoft_FStar_ToSMT_SplitQueryCases.can_handle_query (! (Microsoft_FStar_Options.split_cases)) q)
in (match (_45_3160) with
| (b, cb) -> begin
if b then begin
(Microsoft_FStar_ToSMT_SplitQueryCases.handle_query cb check)
end else begin
(check q)
end
end))
end else begin
(check q)
end)
in (let _45_3161 = if (! (Microsoft_FStar_Options.admit_smt_queries)) then begin
()
end else begin
(process_query qry)
end
in (pop ())))))))
end)
end)))))

let is_trivial = (fun tcenv q -> (let env = (get_env tcenv)
in (let _45_3166 = (push "query")
in (let _45_3173 = (encode_formula_with_labels q env)
in (match (_45_3173) with
| (f, _, _) -> begin
(let _45_3174 = (pop "query")
in (match (f.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.True, _)) -> begin
true
end
| _ -> begin
false
end))
end)))))

let solver = {Microsoft_FStar_Tc_Env.init = init; Microsoft_FStar_Tc_Env.push = push; Microsoft_FStar_Tc_Env.pop = pop; Microsoft_FStar_Tc_Env.mark = mark; Microsoft_FStar_Tc_Env.reset_mark = reset_mark; Microsoft_FStar_Tc_Env.commit_mark = (commit_mark); Microsoft_FStar_Tc_Env.encode_modul = encode_modul; Microsoft_FStar_Tc_Env.encode_sig = encode_sig; Microsoft_FStar_Tc_Env.solve = solve; Microsoft_FStar_Tc_Env.is_trivial = is_trivial; Microsoft_FStar_Tc_Env.finish = Microsoft_FStar_ToSMT_Z3.finish; Microsoft_FStar_Tc_Env.refresh = Microsoft_FStar_ToSMT_Z3.refresh}

let dummy = {Microsoft_FStar_Tc_Env.init = (fun _45_3183 -> ()); Microsoft_FStar_Tc_Env.push = (fun _45_3185 -> ()); Microsoft_FStar_Tc_Env.pop = (fun _45_3187 -> ()); Microsoft_FStar_Tc_Env.mark = (fun _45_3189 -> ()); Microsoft_FStar_Tc_Env.reset_mark = (fun _45_3191 -> ()); Microsoft_FStar_Tc_Env.commit_mark = (fun _45_3193 -> ()); Microsoft_FStar_Tc_Env.encode_modul = (fun _45_3195 _45_3197 -> ()); Microsoft_FStar_Tc_Env.encode_sig = (fun _45_3199 _45_3201 -> ()); Microsoft_FStar_Tc_Env.solve = (fun _45_3203 _45_3205 -> ()); Microsoft_FStar_Tc_Env.is_trivial = (fun _45_3207 _45_3209 -> false); Microsoft_FStar_Tc_Env.finish = (fun _45_3211 -> (match (_45_3211) with
| () -> begin
()
end)); Microsoft_FStar_Tc_Env.refresh = (fun _45_3212 -> (match (_45_3212) with
| () -> begin
()
end))}





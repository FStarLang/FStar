
let add_fuel = (fun x tl -> if (! (Microsoft_FStar_Options.unthrottle_inductives)) then begin
tl
end else begin
(x)::tl
end)

let withenv = (fun c _428367 -> (match (_428367) with
| (a, b) -> begin
(a, b, c)
end))

let vargs = (fun args -> (Support.List.filter (fun _428329 -> (match (_428329) with
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

let primitive_projector_by_pos = (fun env lid i -> (let fail = (fun _428389 -> (match (_428389) with
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
in (let new_scope = (fun _428428 -> (match (_428428) with
| () -> begin
((Support.Microsoft.FStar.Util.smap_create 100), (Support.Microsoft.FStar.Util.smap_create 100))
end))
in (let scopes = (Support.Microsoft.FStar.Util.mk_ref (((new_scope ()))::[]))
in (let mk_unique = (fun y -> (let y = (escape y)
in (let y = (match ((Support.Microsoft.FStar.Util.find_map (! (scopes)) (fun _428436 -> (match (_428436) with
| (names, _) -> begin
(Support.Microsoft.FStar.Util.smap_try_find names y)
end)))) with
| None -> begin
y
end
| Some (_) -> begin
(let _428441 = (Support.Microsoft.FStar.Util.incr ctr)
in (Support.String.strcat (Support.String.strcat y "__") (Support.Microsoft.FStar.Util.string_of_int (! (ctr)))))
end)
in (let top_scope = ((Support.Prims.fst) (Support.List.hd (! (scopes))))
in (let _428445 = (Support.Microsoft.FStar.Util.smap_add top_scope y true)
in y)))))
in (let new_var = (fun pp rn -> (Support.String.strcat (Support.String.strcat (mk_unique pp.Microsoft_FStar_Absyn_Syntax.idText) "__") rn.Microsoft_FStar_Absyn_Syntax.idText))
in (let new_fvar = (fun lid -> (mk_unique lid.Microsoft_FStar_Absyn_Syntax.str))
in (let next_id = (fun _428453 -> (match (_428453) with
| () -> begin
(let _428454 = (Support.Microsoft.FStar.Util.incr ctr)
in (! (ctr)))
end))
in (let fresh = (fun pfx -> (Support.Microsoft.FStar.Util.format2 "%s_%s" pfx (Support.Microsoft.FStar.Util.string_of_int (next_id ()))))
in (let string_const = (fun s -> (match ((Support.Microsoft.FStar.Util.find_map (! (scopes)) (fun _428463 -> (match (_428463) with
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
in (let _428470 = (Support.Microsoft.FStar.Util.smap_add top_scope s f)
in f))))
end))
in (let push = (fun _428473 -> (match (_428473) with
| () -> begin
(scopes := ((new_scope ()))::(! (scopes)))
end))
in (let pop = (fun _428475 -> (match (_428475) with
| () -> begin
(scopes := (Support.List.tl (! (scopes))))
end))
in (let mark = (fun _428477 -> (match (_428477) with
| () -> begin
(push ())
end))
in (let reset_mark = (fun _428479 -> (match (_428479) with
| () -> begin
(pop ())
end))
in (let commit_mark = (fun _428481 -> (match (_428481) with
| () -> begin
(match ((! (scopes))) with
| (hd1, hd2)::(next1, next2)::tl -> begin
(let _428494 = (Support.Microsoft.FStar.Util.smap_fold hd1 (fun key value v -> (Support.Microsoft.FStar.Util.smap_add next1 key value)) ())
in (let _428499 = (Support.Microsoft.FStar.Util.smap_fold hd2 (fun key value v -> (Support.Microsoft.FStar.Util.smap_add next2 key value)) ())
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

let print_env = (fun e -> ((Support.String.concat ", ") ((Support.List.map (fun _428330 -> (match (_428330) with
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
in (ysym, y, (let _428555 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _428555.tcenv; warn = _428555.warn; cache = _428555.cache; nolabels = _428555.nolabels; use_zfuel_name = _428555.use_zfuel_name})))))

let new_term_constant = (fun env x -> (let ysym = (varops.new_var x.Microsoft_FStar_Absyn_Syntax.ppname x.Microsoft_FStar_Absyn_Syntax.realname)
in (let y = (Microsoft_FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _428561 = env
in {bindings = (Binding_var ((x, y)))::env.bindings; depth = _428561.depth; tcenv = _428561.tcenv; warn = _428561.warn; cache = _428561.cache; nolabels = _428561.nolabels; use_zfuel_name = _428561.use_zfuel_name})))))

let push_term_var = (fun env x t -> (let _428566 = env
in {bindings = (Binding_var ((x, t)))::env.bindings; depth = _428566.depth; tcenv = _428566.tcenv; warn = _428566.warn; cache = _428566.cache; nolabels = _428566.nolabels; use_zfuel_name = _428566.use_zfuel_name}))

let lookup_term_var = (fun env a -> (match ((lookup_binding env (fun _428331 -> (match (_428331) with
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
in (ysym, y, (let _428586 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = (env.depth + 1); tcenv = _428586.tcenv; warn = _428586.warn; cache = _428586.cache; nolabels = _428586.nolabels; use_zfuel_name = _428586.use_zfuel_name})))))

let new_typ_constant = (fun env x -> (let ysym = (varops.new_var x.Microsoft_FStar_Absyn_Syntax.ppname x.Microsoft_FStar_Absyn_Syntax.realname)
in (let y = (Microsoft_FStar_ToSMT_Term.mkApp (ysym, []))
in (ysym, y, (let _428592 = env
in {bindings = (Binding_tvar ((x, y)))::env.bindings; depth = _428592.depth; tcenv = _428592.tcenv; warn = _428592.warn; cache = _428592.cache; nolabels = _428592.nolabels; use_zfuel_name = _428592.use_zfuel_name})))))

let push_typ_var = (fun env x t -> (let _428597 = env
in {bindings = (Binding_tvar ((x, t)))::env.bindings; depth = _428597.depth; tcenv = _428597.tcenv; warn = _428597.warn; cache = _428597.cache; nolabels = _428597.nolabels; use_zfuel_name = _428597.use_zfuel_name}))

let lookup_typ_var = (fun env a -> (match ((lookup_binding env (fun _428332 -> (match (_428332) with
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
in (fname, ftok, (let _428617 = env
in {bindings = (Binding_fvar ((x, fname, ((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))), None)))::env.bindings; depth = _428617.depth; tcenv = _428617.tcenv; warn = _428617.warn; cache = _428617.cache; nolabels = _428617.nolabels; use_zfuel_name = _428617.use_zfuel_name})))))

let try_lookup_lid = (fun env a -> (lookup_binding env (fun _428333 -> (match (_428333) with
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

let push_free_var = (fun env x fname ftok -> (let _428639 = env
in {bindings = (Binding_fvar ((x, fname, ftok, None)))::env.bindings; depth = _428639.depth; tcenv = _428639.tcenv; warn = _428639.warn; cache = _428639.cache; nolabels = _428639.nolabels; use_zfuel_name = _428639.use_zfuel_name}))

let push_zfuel_name = (fun env x f -> (let _428648 = (lookup_lid env x)
in (match (_428648) with
| (t1, t2, _) -> begin
(let t3 = (Microsoft_FStar_ToSMT_Term.mkApp (f, ((Microsoft_FStar_ToSMT_Term.mkApp ("ZFuel", [])))::[]))
in (let _428650 = env
in {bindings = (Binding_fvar ((x, t1, t2, Some (t3))))::env.bindings; depth = _428650.depth; tcenv = _428650.tcenv; warn = _428650.warn; cache = _428650.cache; nolabels = _428650.nolabels; use_zfuel_name = _428650.use_zfuel_name}))
end)))

let lookup_free_var = (fun env a -> (let _428657 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_428657) with
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

let lookup_free_var_name = (fun env a -> (let _428681 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_428681) with
| (x, _, _) -> begin
x
end)))

let lookup_free_var_sym = (fun env a -> (let _428687 = (lookup_lid env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_428687) with
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
in (fname, ftok, (let _428714 = env
in {bindings = (Binding_ftvar ((x, fname, ((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_ToSMT_Term.mkApp (ftok, []))))))::env.bindings; depth = _428714.depth; tcenv = _428714.tcenv; warn = _428714.warn; cache = _428714.cache; nolabels = _428714.nolabels; use_zfuel_name = _428714.use_zfuel_name})))))

let lookup_tlid = (fun env a -> (match ((lookup_binding env (fun _428334 -> (match (_428334) with
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

let push_free_tvar = (fun env x fname ftok -> (let _428733 = env
in {bindings = (Binding_ftvar ((x, fname, ftok)))::env.bindings; depth = _428733.depth; tcenv = _428733.tcenv; warn = _428733.warn; cache = _428733.cache; nolabels = _428733.nolabels; use_zfuel_name = _428733.use_zfuel_name}))

let lookup_free_tvar = (fun env a -> (match (((Support.Prims.snd) (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v))) with
| None -> begin
(failwith (Support.Microsoft.FStar.Util.format1 "Type name not found: %s" (Microsoft_FStar_Absyn_Print.sli a.Microsoft_FStar_Absyn_Syntax.v)))
end
| Some (t) -> begin
t
end))

let lookup_free_tvar_name = (fun env a -> ((Support.Prims.fst) (lookup_tlid env a.Microsoft_FStar_Absyn_Syntax.v)))

let tok_of_name = (fun env nm -> (Support.Microsoft.FStar.Util.find_map env.bindings (fun _428335 -> (match (_428335) with
| (Binding_fvar ((_, nm', tok, _))) | (Binding_ftvar ((_, nm', tok))) when (nm = nm') -> begin
tok
end
| _ -> begin
None
end))))

let mkForall_fuel' = (fun n _428763 -> (match (_428763) with
| (pats, vars, body) -> begin
(let fallback = (fun _428765 -> (match (_428765) with
| () -> begin
(Microsoft_FStar_ToSMT_Term.mkForall (pats, vars, body))
end))
in if (! (Microsoft_FStar_Options.unthrottle_inductives)) then begin
(fallback ())
end else begin
(let _428768 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_428768) with
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

let is_app = (fun _428336 -> (match (_428336) with
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

let encode_const = (fun _428337 -> (match (_428337) with
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
(Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkInteger (Support.Microsoft.FStar.Util.int_of_char c)))
end
| Microsoft_FStar_Absyn_Syntax.Const_uint8 (i) -> begin
(Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkInteger (Support.Microsoft.FStar.Util.int_of_uint8 i)))
end
| Microsoft_FStar_Absyn_Syntax.Const_int (i) -> begin
(Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkInteger i))
end
| Microsoft_FStar_Absyn_Syntax.Const_int32 (i) -> begin
(Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkInteger (Support.Microsoft.FStar.Util.int_of_int32 i)))
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
(let _428960 = (encode_binders None bs env)
in (match (_428960) with
| (vars, guards, env', decls, _) -> begin
(let app = (mk_ApplyT t vars)
in (let _428964 = (encode_knd' prekind k env' app)
in (match (_428964) with
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
and encode_binders = (fun fuel_opt bs env -> (let _428975 = if (Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint1 "Encoding binders %s\n" (Microsoft_FStar_Absyn_Print.binders_to_string ", " bs))
end
in (let _429023 = ((Support.List.fold_left (fun _428982 b -> (match (_428982) with
| (vars, guards, env, decls, names) -> begin
(let _429017 = (match ((Support.Prims.fst b)) with
| Support.Microsoft.FStar.Util.Inl ({Microsoft_FStar_Absyn_Syntax.v = a; Microsoft_FStar_Absyn_Syntax.sort = k; Microsoft_FStar_Absyn_Syntax.p = _}) -> begin
(let a = (unmangle a)
in (let _428994 = (gen_typ_var env a)
in (match (_428994) with
| (aasym, aa, env') -> begin
(let _428997 = (encode_knd' false k env aa)
in (match (_428997) with
| (guard_a_k, decls') -> begin
((aasym, Microsoft_FStar_ToSMT_Term.Type_sort), guard_a_k, env', decls', Support.Microsoft.FStar.Util.Inl (a))
end))
end)))
end
| Support.Microsoft.FStar.Util.Inr ({Microsoft_FStar_Absyn_Syntax.v = x; Microsoft_FStar_Absyn_Syntax.sort = t; Microsoft_FStar_Absyn_Syntax.p = _}) -> begin
(let x = (unmangle x)
in (let _429008 = (gen_term_var env x)
in (match (_429008) with
| (xxsym, xx, env') -> begin
(let _429011 = (encode_typ_pred' fuel_opt (norm_t env t) env xx)
in (match (_429011) with
| (guard_x_t, decls') -> begin
((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort), guard_x_t, env', decls', Support.Microsoft.FStar.Util.Inr (x))
end))
end)))
end)
in (match (_429017) with
| (v, g, env, decls', n) -> begin
((v)::vars, (g)::guards, env, (Support.List.append decls decls'), (n)::names)
end))
end)) ([], [], env, [], [])) bs)
in (match (_429023) with
| (vars, guards, env, decls, names) -> begin
((Support.List.rev vars), (Support.List.rev guards), env, decls, (Support.List.rev names))
end))))
and encode_typ_pred' = (fun fuel_opt t env e -> (let t = (Microsoft_FStar_Absyn_Util.compress_typ t)
in (let _429031 = (encode_typ_term t env)
in (match (_429031) with
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
(let _429049 = (encode_binders None binders env)
in (match (_429049) with
| (vars, guards, env', decls, _) -> begin
(let fsym = ((varops.fresh "f"), Microsoft_FStar_ToSMT_Term.Term_sort)
in (let f = (Microsoft_FStar_ToSMT_Term.mkFreeV fsym)
in (let app = (mk_ApplyE f vars)
in (let _429055 = (encode_typ_pred' None (Microsoft_FStar_Absyn_Util.comp_result res) env' app)
in (match (_429055) with
| (res_pred, decls') -> begin
(let t_interp = (Microsoft_FStar_ToSMT_Term.mkForall ((app)::[], vars, (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l guards), res_pred))))
in (let cvars = ((Support.List.filter (fun _429060 -> (match (_429060) with
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
in (let _429081 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
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
(let _429111 = (match ((Microsoft_FStar_Tc_Normalize.normalize_refinement env.tcenv t0)) with
| {Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Typ_refine ((x, f)); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _} -> begin
(x, f)
end
| _ -> begin
(failwith "impossible")
end)
in (match (_429111) with
| (x, f) -> begin
(let _429114 = (encode_typ_term x.Microsoft_FStar_Absyn_Syntax.sort env)
in (match (_429114) with
| (base_t, decls) -> begin
(let _429118 = (gen_term_var env x.Microsoft_FStar_Absyn_Syntax.v)
in (match (_429118) with
| (x, xtm, env') -> begin
(let _429121 = (encode_formula f env')
in (match (_429121) with
| (refinement, decls') -> begin
(let encoding = (Microsoft_FStar_ToSMT_Term.mkAnd ((Microsoft_FStar_ToSMT_Term.mk_HasType xtm base_t), refinement))
in (let cvars = ((Support.List.filter (fun _429126 -> (match (_429126) with
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
in (let _429147 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls)))))))))))
end)))))
end))
end))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_uvar ((uv, k)) -> begin
(let ttm = (Microsoft_FStar_ToSMT_Term.mk_Typ_uvar (Support.Microsoft.FStar.Unionfind.uvar_id uv))
in (let _429156 = (encode_knd k env ttm)
in (match (_429156) with
| (t_has_k, decls) -> begin
(let d = Microsoft_FStar_ToSMT_Term.Assume ((t_has_k, None))
in (ttm, (d)::decls))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_app ((head, args)) -> begin
(let is_full_app = (fun _429163 -> (match (_429163) with
| () -> begin
(let kk = (Microsoft_FStar_Tc_Recheck.recompute_kind head)
in (let _429168 = (Microsoft_FStar_Absyn_Util.kind_formals kk)
in (match (_429168) with
| (formals, _) -> begin
((Support.List.length formals) = (Support.List.length args))
end)))
end))
in (let head = (Microsoft_FStar_Absyn_Util.compress_typ head)
in (match (head.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_btvar (a) -> begin
(let head = (lookup_typ_var env a)
in (let _429175 = (encode_args args env)
in (match (_429175) with
| (args, decls) -> begin
(let t = (mk_ApplyT_args head args)
in (t, decls))
end)))
end
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let _429181 = (encode_args args env)
in (match (_429181) with
| (args, decls) -> begin
if (is_full_app ()) then begin
(let head = (lookup_free_tvar_name env fv)
in (let t = (Microsoft_FStar_ToSMT_Term.mkApp (head, (Support.List.map (fun _428338 -> (match (_428338) with
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
in (let _429197 = (encode_knd k env ttm)
in (match (_429197) with
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
(let _429212 = (encode_binders None bs env)
in (match (_429212) with
| (vars, guards, env, decls, _) -> begin
(let _429215 = (encode_typ_term body env)
in (match (_429215) with
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
in (let kinding = (let _429238 = (encode_knd (Microsoft_FStar_Tc_Recheck.recompute_kind t0) env t)
in (match (_429238) with
| (ktm, decls'') -> begin
(Support.List.append decls'' ((Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((t)::[], cvars, ktm)), Some ("Typ_lam kinding"))))::[]))
end))
in (let t_decls = (Support.List.append (Support.List.append decls decls') ((tdecl)::(interp)::kinding))
in (let _429241 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (tsym, cvar_sorts, t_decls))
in (t, t_decls))))))))))
end)
end))))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Typ_ascribed ((t, _)) -> begin
(encode_typ_term t env)
end
| (Microsoft_FStar_Absyn_Syntax.Typ_meta (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_delayed (_)) | (Microsoft_FStar_Absyn_Syntax.Typ_unknown) -> begin
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
(let _429276 = (e.Microsoft_FStar_Absyn_Syntax.tk := Some (t))
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
(let fallback = (fun _429295 -> (match (_429295) with
| () -> begin
(let f = (varops.fresh "Exp_abs")
in (let decl = Microsoft_FStar_ToSMT_Term.DeclFun ((f, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in ((Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort)), (decl)::[])))
end))
in (match ((! (e.Microsoft_FStar_Absyn_Syntax.tk))) with
| None -> begin
(let _429299 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Losing precision when encoding a function literal")
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
(let _429311 = (Support.Microsoft.FStar.Util.first_N nformals bs)
in (match (_429311) with
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
(let _429324 = (encode_binders None bs env)
in (match (_429324) with
| (vars, guards, envbody, decls, _) -> begin
(let _429327 = (encode_exp body envbody)
in (match (_429327) with
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
in (let _429349 = (encode_typ_pred' None tfun env f)
in (match (_429349) with
| (f_has_t, decls'') -> begin
(let typing_f = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((f)::[], cvars, f_has_t)), Some ((Support.String.strcat fsym " typing"))))
in (let interp_f = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((app)::[], (Support.List.append vars cvars), (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_IsTyped app), (Microsoft_FStar_ToSMT_Term.mkEq (app, body)))))), Some ((Support.String.strcat fsym " interpretation"))))
in (let f_decls = (Support.List.append (Support.List.append (Support.List.append decls decls') ((fdecl)::decls'')) ((typing_f)::(interp_f)::[]))
in (let _429353 = (Support.Microsoft.FStar.Util.smap_add env.cache tkey.Microsoft_FStar_ToSMT_Term.hash (fsym, cvar_sorts, f_decls))
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
(let _429392 = (encode_exp v1 env)
in (match (_429392) with
| (v1, decls1) -> begin
(let _429395 = (encode_exp v2 env)
in (match (_429395) with
| (v2, decls2) -> begin
((Microsoft_FStar_ToSMT_Term.mk_LexCons v1 v2), (Support.List.append decls1 decls2))
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_app (({Microsoft_FStar_Absyn_Syntax.n = Microsoft_FStar_Absyn_Syntax.Exp_abs (_); Microsoft_FStar_Absyn_Syntax.tk = _; Microsoft_FStar_Absyn_Syntax.pos = _; Microsoft_FStar_Absyn_Syntax.fvs = _; Microsoft_FStar_Absyn_Syntax.uvs = _}, _)) -> begin
(encode_exp (whnf_e env e) env)
end
| Microsoft_FStar_Absyn_Syntax.Exp_app ((head, args_e)) -> begin
(let _429418 = (encode_args args_e env)
in (match (_429418) with
| (args, decls) -> begin
(let encode_partial_app = (fun ht_opt -> (let _429423 = (encode_exp head env)
in (match (_429423) with
| (head, decls') -> begin
(let app_tm = (mk_ApplyE_args head args)
in (match (ht_opt) with
| None -> begin
(app_tm, (Support.List.append decls decls'))
end
| Some ((formals, c)) -> begin
(let _429432 = (Support.Microsoft.FStar.Util.first_N (Support.List.length args_e) formals)
in (match (_429432) with
| (formals, rest) -> begin
(let subst = (Microsoft_FStar_Absyn_Util.formals_for_actuals formals args_e)
in (let ty = ((Microsoft_FStar_Absyn_Util.subst_typ subst) (Microsoft_FStar_Absyn_Syntax.mk_Typ_fun (rest, c) (Some (Microsoft_FStar_Absyn_Syntax.ktype)) e0.Microsoft_FStar_Absyn_Syntax.pos))
in (let _429437 = (encode_typ_pred' None ty env app_tm)
in (match (_429437) with
| (has_type, decls'') -> begin
(let cvars = (Microsoft_FStar_ToSMT_Term.free_variables has_type)
in (let e_typing = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((has_type)::[], cvars, has_type)), None))
in (app_tm, (Support.List.append (Support.List.append (Support.List.append decls decls') decls'') ((e_typing)::[])))))
end))))
end))
end))
end)))
in (let encode_full_app = (fun fv -> (let _429444 = (lookup_free_var_sym env fv)
in (match (_429444) with
| (fname, fuel_args) -> begin
(let tm = (Microsoft_FStar_ToSMT_Term.mkApp' (fname, (Support.List.append fuel_args (Support.List.map (fun _428339 -> (match (_428339) with
| (Support.Microsoft.FStar.Util.Inl (t)) | (Support.Microsoft.FStar.Util.Inr (t)) -> begin
t
end)) args))))
in (tm, decls))
end)))
in (let head = (Microsoft_FStar_Absyn_Util.compress_exp head)
in (let _429451 = if ((Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("186"))) then begin
(Support.Microsoft.FStar.Util.fprint2 "Recomputing type for %s\nFull term is %s\n" (Microsoft_FStar_Absyn_Print.exp_to_string head) (Microsoft_FStar_Absyn_Print.exp_to_string e))
end
in (let head_type = (Microsoft_FStar_Absyn_Util.unrefine (whnf env (Microsoft_FStar_Absyn_Util.unrefine (Microsoft_FStar_Tc_Recheck.recompute_typ head))))
in (let _429454 = if ((Microsoft_FStar_Tc_Env.debug env.tcenv) (Microsoft_FStar_Options.Other ("Encoding"))) then begin
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
(let _429496 = (encode_exp e1 env)
in (match (_429496) with
| (ee1, decls1) -> begin
(let env' = (push_term_var env x ee1)
in (let _429500 = (encode_exp e2 env')
in (match (_429500) with
| (ee2, decls2) -> begin
(ee2, (Support.List.append decls1 decls2))
end)))
end))
end
| Microsoft_FStar_Absyn_Syntax.Exp_let (_) -> begin
(let _429504 = (Microsoft_FStar_Tc_Errors.warn e.Microsoft_FStar_Absyn_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts")
in (let e = (varops.fresh "let-rec")
in (let decl_e = Microsoft_FStar_ToSMT_Term.DeclFun ((e, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in ((Microsoft_FStar_ToSMT_Term.mkFreeV (e, Microsoft_FStar_ToSMT_Term.Term_sort)), (decl_e)::[]))))
end
| Microsoft_FStar_Absyn_Syntax.Exp_match ((e, pats)) -> begin
(let _429514 = (encode_exp e env)
in (match (_429514) with
| (scr, decls) -> begin
(let _429554 = (Support.List.fold_right (fun _429518 _429521 -> (match ((_429518, _429521)) with
| ((p, w, br), (else_case, decls)) -> begin
(let patterns = (encode_pat env p)
in (Support.List.fold_right (fun _429525 _429528 -> (match ((_429525, _429528)) with
| ((env0, pattern), (else_case, decls)) -> begin
(let guard = (pattern.guard scr)
in (let projections = (pattern.projections scr)
in (let env = ((Support.List.fold_left (fun env _429534 -> (match (_429534) with
| (x, t) -> begin
(match (x) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(push_typ_var env a.Microsoft_FStar_Absyn_Syntax.v t)
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(push_term_var env x.Microsoft_FStar_Absyn_Syntax.v t)
end)
end)) env) projections)
in (let _429548 = (match (w) with
| None -> begin
(guard, [])
end
| Some (w) -> begin
(let _429545 = (encode_exp w env)
in (match (_429545) with
| (w, decls2) -> begin
((Microsoft_FStar_ToSMT_Term.mkAnd (guard, (Microsoft_FStar_ToSMT_Term.mkEq (w, (Microsoft_FStar_ToSMT_Term.boxBool Microsoft_FStar_ToSMT_Term.mkTrue))))), decls2)
end))
end)
in (match (_429548) with
| (guard, decls2) -> begin
(let _429551 = (encode_exp br env)
in (match (_429551) with
| (br, decls3) -> begin
((Microsoft_FStar_ToSMT_Term.mkITE (guard, br, else_case)), (Support.List.append (Support.List.append decls decls2) decls3))
end))
end)))))
end)) patterns (else_case, decls)))
end)) pats (Microsoft_FStar_ToSMT_Term.mk_Term_unit, decls))
in (match (_429554) with
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
and encode_one_pat = (fun env pat -> (let _429566 = if (Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint1 "Encoding pattern %s\n" (Microsoft_FStar_Absyn_Print.pat_to_string pat))
end
in (let _429570 = (Microsoft_FStar_Tc_Util.decorated_pattern_as_either pat)
in (match (_429570) with
| (vars, pat_exp_or_typ) -> begin
(let _429591 = ((Support.List.fold_left (fun _429573 v -> (match (_429573) with
| (env, vars) -> begin
(match (v) with
| Support.Microsoft.FStar.Util.Inl (a) -> begin
(let _429581 = (gen_typ_var env a.Microsoft_FStar_Absyn_Syntax.v)
in (match (_429581) with
| (aa, _, env) -> begin
(env, ((v, (aa, Microsoft_FStar_ToSMT_Term.Type_sort)))::vars)
end))
end
| Support.Microsoft.FStar.Util.Inr (x) -> begin
(let _429588 = (gen_term_var env x.Microsoft_FStar_Absyn_Syntax.v)
in (match (_429588) with
| (xx, _, env) -> begin
(env, ((v, (xx, Microsoft_FStar_ToSMT_Term.Term_sort)))::vars)
end))
end)
end)) (env, [])) vars)
in (match (_429591) with
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
in (let pat_term = (fun _429661 -> (match (_429661) with
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
and encode_args = (fun l env -> (let _429691 = ((Support.List.fold_left (fun _429671 x -> (match (_429671) with
| (tms, decls) -> begin
(match (x) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(let _429680 = (encode_typ_term t env)
in (match (_429680) with
| (t, decls') -> begin
((Support.Microsoft.FStar.Util.Inl (t))::tms, (Support.List.append decls decls'))
end))
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(let _429688 = (encode_exp e env)
in (match (_429688) with
| (t, decls') -> begin
((Support.Microsoft.FStar.Util.Inr (t))::tms, (Support.List.append decls decls'))
end))
end)
end)) ([], [])) l)
in (match (_429691) with
| (l, decls) -> begin
((Support.List.rev l), decls)
end)))
and encode_formula = (fun phi env -> (let _429697 = (encode_formula_with_labels phi env)
in (match (_429697) with
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
in (let _429793 = (match ((Microsoft_FStar_Absyn_Util.compress_typ t).Microsoft_FStar_Absyn_Syntax.n) with
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
in (match (_429793) with
| (binders, pre, post, patterns) -> begin
(let _429800 = (encode_binders None binders env)
in (match (_429800) with
| (vars, guards, env, decls, _) -> begin
(let _429816 = ((Support.List.unzip) ((Support.List.map (fun _428340 -> (match (_428340) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(encode_formula t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(encode_exp e (let _429812 = env
in {bindings = _429812.bindings; depth = _429812.depth; tcenv = _429812.tcenv; warn = _429812.warn; cache = _429812.cache; nolabels = _429812.nolabels; use_zfuel_name = true}))
end))) patterns))
in (match (_429816) with
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
in (let env = (let _429837 = env
in {bindings = _429837.bindings; depth = _429837.depth; tcenv = _429837.tcenv; warn = _429837.warn; cache = _429837.cache; nolabels = true; use_zfuel_name = _429837.use_zfuel_name})
in (let _429842 = (encode_formula (Microsoft_FStar_Absyn_Util.unmeta_typ pre) env)
in (match (_429842) with
| (pre, decls'') -> begin
(let _429845 = (encode_formula (Microsoft_FStar_Absyn_Util.unmeta_typ post) env)
in (match (_429845) with
| (post, decls''') -> begin
(let decls = (Support.List.append (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls'') decls''')
in ((Microsoft_FStar_ToSMT_Term.mkForall (pats, vars, (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l ((pre)::guards)), post)))), decls))
end))
end))))
end))
end))
end)))))
and encode_formula_with_labels = (fun phi env -> (let enc = (fun f l -> (let _429866 = (Support.Microsoft.FStar.Util.fold_map (fun decls x -> (match ((Support.Prims.fst x)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _429858 = (encode_typ_term t env)
in (match (_429858) with
| (t, decls') -> begin
((Support.List.append decls decls'), t)
end))
end
| Support.Microsoft.FStar.Util.Inr (e) -> begin
(let _429863 = (encode_exp e env)
in (match (_429863) with
| (e, decls') -> begin
((Support.List.append decls decls'), e)
end))
end)) [] l)
in (match (_429866) with
| (decls, args) -> begin
((f args), [], decls)
end)))
in (let enc_prop_c = (fun f l -> (let _429886 = (Support.List.fold_right (fun t _429874 -> (match (_429874) with
| (phis, labs, decls) -> begin
(match ((Support.Prims.fst t)) with
| Support.Microsoft.FStar.Util.Inl (t) -> begin
(let _429880 = (encode_formula_with_labels t env)
in (match (_429880) with
| (phi, labs', decls') -> begin
((phi)::phis, (Support.List.append labs' labs), (Support.List.append decls' decls))
end))
end
| _ -> begin
(failwith "Expected a formula")
end)
end)) l ([], [], []))
in (match (_429886) with
| (phis, labs, decls) -> begin
((f phis), labs, decls)
end)))
in (let const_op = (fun f _429889 -> (f, [], []))
in (let un_op = (fun f l -> (f (Support.List.hd l)))
in (let bin_op = (fun f _428341 -> (match (_428341) with
| t1::t2::[] -> begin
(f (t1, t2))
end
| _ -> begin
(failwith "Impossible")
end))
in (let tri_op = (fun f _428342 -> (match (_428342) with
| t1::t2::t3::[] -> begin
(f (t1, t2, t3))
end
| _ -> begin
(failwith "Impossible")
end))
in (let eq_op = (fun _428343 -> (match (_428343) with
| _::_::e1::e2::[] -> begin
(enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq) ((e1)::(e2)::[]))
end
| l -> begin
(enc (bin_op Microsoft_FStar_ToSMT_Term.mkEq) l)
end))
in (let mk_imp = (fun _428344 -> (match (_428344) with
| (Support.Microsoft.FStar.Util.Inl (lhs), _)::(Support.Microsoft.FStar.Util.Inl (rhs), _)::[] -> begin
(let _429936 = (encode_formula_with_labels rhs env)
in (match (_429936) with
| (l1, labs1, decls1) -> begin
(match (l1.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.True, _)) -> begin
(l1, labs1, decls1)
end
| _ -> begin
(let _429947 = (encode_formula_with_labels lhs env)
in (match (_429947) with
| (l2, labs2, decls2) -> begin
((Microsoft_FStar_ToSMT_Term.mkImp (l2, l1)), (Support.List.append labs1 labs2), (Support.List.append decls1 decls2))
end))
end)
end))
end
| _ -> begin
(failwith "impossible")
end))
in (let mk_ite = (fun _428345 -> (match (_428345) with
| (Support.Microsoft.FStar.Util.Inl (guard), _)::(Support.Microsoft.FStar.Util.Inl (_then), _)::(Support.Microsoft.FStar.Util.Inl (_else), _)::[] -> begin
(let _429971 = (encode_formula_with_labels guard env)
in (match (_429971) with
| (g, labs1, decls1) -> begin
(let _429975 = (encode_formula_with_labels _then env)
in (match (_429975) with
| (t, labs2, decls2) -> begin
(let _429979 = (encode_formula_with_labels _else env)
in (match (_429979) with
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
(let _430000 = (encode_formula_with_labels phi' env)
in (match (_430000) with
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
(let _430032 = (encode_exp l env)
in (match (_430032) with
| (e, decls) -> begin
(let _430035 = (encode_function_type_as_formula (Some (e)) phi env)
in (match (_430035) with
| (f, decls') -> begin
(f, [], (Support.List.append decls decls'))
end))
end))
end else begin
(Microsoft_FStar_ToSMT_Term.mkTrue, [], [])
end
end
| _ -> begin
(let _430040 = (encode_typ_term phi env)
in (match (_430040) with
| (tt, decls) -> begin
((Microsoft_FStar_ToSMT_Term.mk_Valid tt), [], decls)
end))
end))
in (let encode_q_body = (fun env bs ps body -> (let _430052 = (encode_binders None bs env)
in (match (_430052) with
| (vars, guards, env, decls, _) -> begin
(let _430068 = ((Support.List.unzip) ((Support.List.map (fun _428346 -> (match (_428346) with
| (Support.Microsoft.FStar.Util.Inl (t), _) -> begin
(encode_formula t env)
end
| (Support.Microsoft.FStar.Util.Inr (e), _) -> begin
(encode_exp e (let _430064 = env
in {bindings = _430064.bindings; depth = _430064.depth; tcenv = _430064.tcenv; warn = _430064.warn; cache = _430064.cache; nolabels = _430064.nolabels; use_zfuel_name = true}))
end))) ps))
in (match (_430068) with
| (pats, decls') -> begin
(let _430072 = (encode_formula_with_labels body env)
in (match (_430072) with
| (body, labs, decls'') -> begin
(vars, pats, (Microsoft_FStar_ToSMT_Term.mk_and_l guards), body, labs, (Support.List.append (Support.List.append decls (Support.List.flatten decls')) decls''))
end))
end))
end)))
in (let _430073 = if (Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint1 ">>>> Destructing as formula ... %s\n" (Microsoft_FStar_Absyn_Print.formula_to_string phi))
end
in (let phi = (Microsoft_FStar_Absyn_Util.compress_typ phi)
in (match ((Microsoft_FStar_Absyn_Util.destruct_typ_as_formula phi)) with
| None -> begin
(fallback phi)
end
| Some (Microsoft_FStar_Absyn_Util.BaseConn ((op, arms))) -> begin
(match (((Support.List.tryFind (fun _430085 -> (match (_430085) with
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
(let _430098 = if (Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint1 ">>>> Got QALL [%s]\n" ((Microsoft_FStar_Absyn_Print.binders_to_string "; ") vars))
end
in (let _430106 = (encode_q_body env vars pats body)
in (match (_430106) with
| (vars, pats, guard, body, labs, decls) -> begin
((Microsoft_FStar_ToSMT_Term.mkForall (pats, vars, (Microsoft_FStar_ToSMT_Term.mkImp (guard, body)))), labs, decls)
end)))
end
| Some (Microsoft_FStar_Absyn_Util.QEx ((vars, pats, body))) -> begin
(let _430119 = (encode_q_body env vars pats body)
in (match (_430119) with
| (vars, pats, guard, body, labs, decls) -> begin
((Microsoft_FStar_ToSMT_Term.mkExists (pats, vars, (Microsoft_FStar_ToSMT_Term.mkAnd (guard, body)))), labs, decls)
end))
end)))))))))))))))))

type prims_t =
{mk : Microsoft_FStar_Absyn_Syntax.lident  ->  string  ->  Microsoft_FStar_ToSMT_Term.decl list; is : Microsoft_FStar_Absyn_Syntax.lident  ->  bool}

let prims = (let _430125 = (fresh_fvar "a" Microsoft_FStar_ToSMT_Term.Type_sort)
in (match (_430125) with
| (asym, a) -> begin
(let _430128 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_430128) with
| (xsym, x) -> begin
(let _430131 = (fresh_fvar "y" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_430131) with
| (ysym, y) -> begin
(let deffun = (fun vars body x -> (Microsoft_FStar_ToSMT_Term.DefineFun ((x, vars, Microsoft_FStar_ToSMT_Term.Term_sort, body, None)))::[])
in (let quant = (fun vars body x -> (let t1 = (Microsoft_FStar_ToSMT_Term.mkApp (x, (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)))
in (let vname_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((x, ((Support.List.map (Support.Prims.snd)) vars), Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (vname_decl)::(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((t1)::[], vars, (Microsoft_FStar_ToSMT_Term.mkEq (t1, body)))), None)))::[])))
in (let axy = ((asym, Microsoft_FStar_ToSMT_Term.Type_sort))::((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let xy = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::((ysym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let qx = ((xsym, Microsoft_FStar_ToSMT_Term.Term_sort))::[]
in (let prims = ((Microsoft_FStar_Absyn_Const.op_Eq, (quant axy (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkEq (x, y))))))::((Microsoft_FStar_Absyn_Const.op_notEq, (quant axy (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkNot (Microsoft_FStar_ToSMT_Term.mkEq (x, y)))))))::((Microsoft_FStar_Absyn_Const.op_LT, (quant xy (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkLT ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_LTE, (quant xy (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkLTE ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_GT, (quant xy (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkGT ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_GTE, (quant xy (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkGTE ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_Subtraction, (quant xy (Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkSub ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_Minus, (quant qx (Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkMinus (Microsoft_FStar_ToSMT_Term.unboxInt x))))))::((Microsoft_FStar_Absyn_Const.op_Addition, (quant xy (Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkAdd ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_Multiply, (quant xy (Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkMul ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_Division, (quant xy (Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkDiv ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_Modulus, (quant xy (Microsoft_FStar_ToSMT_Term.boxInt (Microsoft_FStar_ToSMT_Term.mkMod ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.unboxInt y)))))))::((Microsoft_FStar_Absyn_Const.op_And, (quant xy (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkAnd ((Microsoft_FStar_ToSMT_Term.unboxBool x), (Microsoft_FStar_ToSMT_Term.unboxBool y)))))))::((Microsoft_FStar_Absyn_Const.op_Or, (quant xy (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkOr ((Microsoft_FStar_ToSMT_Term.unboxBool x), (Microsoft_FStar_ToSMT_Term.unboxBool y)))))))::((Microsoft_FStar_Absyn_Const.op_Negation, (quant qx (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mkNot (Microsoft_FStar_ToSMT_Term.unboxBool x))))))::[]
in (let mk = (fun l v -> ((Support.List.collect (fun _430155 -> (match (_430155) with
| (_, b) -> begin
(b v)
end))) ((Support.List.filter (fun _430151 -> (match (_430151) with
| (l', _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l l')
end))) prims)))
in (let is = (fun l -> ((Support.Microsoft.FStar.Util.for_some (fun _430161 -> (match (_430161) with
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
in (let mk_unit = (fun _430167 tt -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mk_HasType Microsoft_FStar_ToSMT_Term.mk_Term_unit tt), Some ("unit typing"))))::(Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel ((typing_pred)::[], (xx)::[], (Microsoft_FStar_ToSMT_Term.mkImp (typing_pred, (Microsoft_FStar_ToSMT_Term.mkEq (x, Microsoft_FStar_ToSMT_Term.mk_Term_unit)))))), Some ("unit inversion"))))::[]))
in (let mk_bool = (fun _430172 tt -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Bool_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel ((typing_pred)::[], (xx)::[], (Microsoft_FStar_ToSMT_Term.mkImp (typing_pred, (Microsoft_FStar_ToSMT_Term.mk_tester "BoxBool" x))))), Some ("bool inversion"))))::(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall (((Microsoft_FStar_ToSMT_Term.boxBool b))::[], (bb)::[], (Microsoft_FStar_ToSMT_Term.mk_HasType (Microsoft_FStar_ToSMT_Term.boxBool b) tt))), Some ("bool typing"))))::[]))))
in (let mk_int = (fun _430179 tt -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let typing_pred_y = (Microsoft_FStar_ToSMT_Term.mk_HasType y tt)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let a = (Microsoft_FStar_ToSMT_Term.mkFreeV aa)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Int_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (let precedes = (Microsoft_FStar_ToSMT_Term.mk_Valid (Microsoft_FStar_ToSMT_Term.mkApp ("Prims.Precedes", (tt)::(tt)::((Microsoft_FStar_ToSMT_Term.boxInt a))::((Microsoft_FStar_ToSMT_Term.boxInt b))::[])))
in (let precedes_y_x = (Microsoft_FStar_ToSMT_Term.mk_Valid (Microsoft_FStar_ToSMT_Term.mkApp ("Precedes", (y)::(x)::[])))
in (Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel ((typing_pred)::[], (xx)::[], (Microsoft_FStar_ToSMT_Term.mkImp (typing_pred, (Microsoft_FStar_ToSMT_Term.mk_tester "BoxInt" x))))), Some ("int inversion"))))::(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall (((Microsoft_FStar_ToSMT_Term.boxInt b))::[], (bb)::[], (Microsoft_FStar_ToSMT_Term.mk_HasType (Microsoft_FStar_ToSMT_Term.boxInt b) tt))), Some ("int typing"))))::(Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel ((typing_pred)::(typing_pred_y)::(precedes_y_x)::[], (xx)::(yy)::[], (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l ((typing_pred)::(typing_pred_y)::((Microsoft_FStar_ToSMT_Term.mkGT ((Microsoft_FStar_ToSMT_Term.unboxInt x), (Microsoft_FStar_ToSMT_Term.mkInteger 0))))::((Microsoft_FStar_ToSMT_Term.mkGTE ((Microsoft_FStar_ToSMT_Term.unboxInt y), (Microsoft_FStar_ToSMT_Term.mkInteger 0))))::((Microsoft_FStar_ToSMT_Term.mkLT ((Microsoft_FStar_ToSMT_Term.unboxInt y), (Microsoft_FStar_ToSMT_Term.unboxInt x))))::[])), precedes_y_x)))), Some ("well-founded ordering on nat (alt)"))))::[])))))))))
in (let mk_int_alias = (fun _430191 tt -> (Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkEq (tt, (Microsoft_FStar_ToSMT_Term.mkApp (Microsoft_FStar_Absyn_Const.int_lid.Microsoft_FStar_Absyn_Syntax.str, [])))), Some ("mapping to int; for now"))))::[])
in (let mk_str = (fun _430195 tt -> (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x tt)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.String_sort)
in (let b = (Microsoft_FStar_ToSMT_Term.mkFreeV bb)
in (Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel ((typing_pred)::[], (xx)::[], (Microsoft_FStar_ToSMT_Term.mkImp (typing_pred, (Microsoft_FStar_ToSMT_Term.mk_tester "BoxString" x))))), Some ("string inversion"))))::(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall (((Microsoft_FStar_ToSMT_Term.boxString b))::[], (bb)::[], (Microsoft_FStar_ToSMT_Term.mk_HasType (Microsoft_FStar_ToSMT_Term.boxString b) tt))), Some ("string typing"))))::[]))))
in (let mk_ref = (fun reft_name _430203 -> (let r = ("r", Microsoft_FStar_ToSMT_Term.Ref_sort)
in (let aa = ("a", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let bb = ("b", Microsoft_FStar_ToSMT_Term.Type_sort)
in (let refa = (Microsoft_FStar_ToSMT_Term.mkApp (reft_name, ((Microsoft_FStar_ToSMT_Term.mkFreeV aa))::[]))
in (let refb = (Microsoft_FStar_ToSMT_Term.mkApp (reft_name, ((Microsoft_FStar_ToSMT_Term.mkFreeV bb))::[]))
in (let typing_pred = (Microsoft_FStar_ToSMT_Term.mk_HasType x refa)
in (let typing_pred_b = (Microsoft_FStar_ToSMT_Term.mk_HasType x refb)
in (Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel ((typing_pred)::[], (xx)::(aa)::[], (Microsoft_FStar_ToSMT_Term.mkImp (typing_pred, (Microsoft_FStar_ToSMT_Term.mk_tester "BoxRef" x))))), Some ("ref inversion"))))::(Microsoft_FStar_ToSMT_Term.Assume (((mkForall_fuel' 2 ((typing_pred)::(typing_pred_b)::[], (xx)::(aa)::(bb)::[], (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mkAnd (typing_pred, typing_pred_b)), (Microsoft_FStar_ToSMT_Term.mkEq ((Microsoft_FStar_ToSMT_Term.mkFreeV aa), (Microsoft_FStar_ToSMT_Term.mkFreeV bb))))))), Some ("ref typing is injective"))))::[]))))))))
in (let prims = ((Microsoft_FStar_Absyn_Const.unit_lid, mk_unit))::((Microsoft_FStar_Absyn_Const.bool_lid, mk_bool))::((Microsoft_FStar_Absyn_Const.int_lid, mk_int))::((Microsoft_FStar_Absyn_Const.string_lid, mk_str))::((Microsoft_FStar_Absyn_Const.ref_lid, mk_ref))::((Microsoft_FStar_Absyn_Const.char_lid, mk_int_alias))::((Microsoft_FStar_Absyn_Const.uint8_lid, mk_int_alias))::[]
in (fun t s tt -> (match ((Support.Microsoft.FStar.Util.find_opt (fun _430220 -> (match (_430220) with
| (l, _) -> begin
(Microsoft_FStar_Absyn_Syntax.lid_equals l t)
end)) prims)) with
| None -> begin
[]
end
| Some ((_, f)) -> begin
(f s tt)
end)))))))))))))

let rec encode_sigelt = (fun env se -> (let _430229 = if (Microsoft_FStar_Tc_Env.debug env.tcenv Microsoft_FStar_Options.Low) then begin
((Support.Microsoft.FStar.Util.fprint1 ">>>>Encoding [%s]\n") (Microsoft_FStar_Absyn_Print.sigelt_to_string se))
end
in (let nm = (match ((Microsoft_FStar_Absyn_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.Microsoft_FStar_Absyn_Syntax.str
end)
in (let _430237 = (encode_sigelt' env se)
in (match (_430237) with
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
(let _430288 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_430288) with
| (tname, ttok, env) -> begin
(let xx = ("x", Microsoft_FStar_ToSMT_Term.Term_sort)
in (let x = (Microsoft_FStar_ToSMT_Term.mkFreeV xx)
in (let valid_b2t_x = (Microsoft_FStar_ToSMT_Term.mk_Valid (Microsoft_FStar_ToSMT_Term.mkApp ("Prims.b2t", (x)::[])))
in (let decls = (Microsoft_FStar_ToSMT_Term.DeclFun ((tname, (Microsoft_FStar_ToSMT_Term.Term_sort)::[], Microsoft_FStar_ToSMT_Term.Type_sort, None)))::(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((valid_b2t_x)::[], (xx)::[], (Microsoft_FStar_ToSMT_Term.mkEq (valid_b2t_x, (Microsoft_FStar_ToSMT_Term.mkApp ("BoxBool_proj_0", (x)::[])))))), Some ("b2t def"))))::[]
in (decls, env)))))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_typ_abbrev ((lid, tps, _, t, tags, _)) -> begin
(let _430306 = (new_typ_constant_and_tok_from_lid env lid)
in (match (_430306) with
| (tname, ttok, env) -> begin
(let _430315 = (match (t.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_lam ((tps', body)) -> begin
((Support.List.append tps tps'), body)
end
| _ -> begin
(tps, t)
end)
in (match (_430315) with
| (tps, t) -> begin
(let _430322 = (encode_binders None tps env)
in (match (_430322) with
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
in (let _430340 = if ((Support.Microsoft.FStar.Util.for_some (fun _428347 -> (match (_428347) with
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
in (match (_430340) with
| (def, (body, decls1)) -> begin
(let abbrev_def = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((def)::[], vars, (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l guards), (Microsoft_FStar_ToSMT_Term.mkEq (def, body)))))), Some ("abbrev. elimination")))
in (let kindingAx = (let _430344 = (encode_knd (Microsoft_FStar_Tc_Recheck.recompute_kind t) env' app)
in (match (_430344) with
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
in (let _430357 = (encode_free_var env lid t tt quals)
in (match (_430357) with
| (decls, env) -> begin
if ((Microsoft_FStar_Absyn_Util.is_smt_lemma t) && (((Support.List.contains Microsoft_FStar_Absyn_Syntax.Assumption) quals) || env.tcenv.Microsoft_FStar_Tc_Env.is_iface)) then begin
((Support.List.append decls (encode_smt_lemma env lid t)), env)
end else begin
(decls, env)
end
end)))
end
| Microsoft_FStar_Absyn_Syntax.Sig_assume ((l, f, _, _)) -> begin
(let _430368 = (encode_formula f env)
in (match (_430368) with
| (f, decls) -> begin
(let g = (Microsoft_FStar_ToSMT_Term.Assume ((f, Some ((Support.Microsoft.FStar.Util.format1 "Assumption: %s" (Microsoft_FStar_Absyn_Print.sli l))))))::[]
in ((Support.List.append decls g), env))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_tycon ((t, tps, k, _, datas, quals, _)) when (Microsoft_FStar_Absyn_Syntax.lid_equals t Microsoft_FStar_Absyn_Const.precedes_lid) -> begin
(let _430384 = (new_typ_constant_and_tok_from_lid env t)
in (match (_430384) with
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
(let is_logical = ((Support.Microsoft.FStar.Util.for_some (fun _428348 -> (match (_428348) with
| (Microsoft_FStar_Absyn_Syntax.Logic) | (Microsoft_FStar_Absyn_Syntax.Assumption) -> begin
true
end
| _ -> begin
false
end))) quals)
in (let constructor_or_logic_type_decl = (fun c -> if is_logical then begin
(let _430428 = c
in (match (_430428) with
| (name, args, _, _) -> begin
(Microsoft_FStar_ToSMT_Term.DeclFun ((name, ((Support.List.map (Support.Prims.snd)) args), Microsoft_FStar_ToSMT_Term.Type_sort, None)))::[]
end))
end else begin
(Microsoft_FStar_ToSMT_Term.constructor_to_decl c)
end)
in (let inversion_axioms = (fun tapp vars -> if (((Support.List.length datas) = 0) || ((Support.Microsoft.FStar.Util.for_some (fun l -> ((Support.Option.isNone) (Microsoft_FStar_Tc_Env.lookup_qname env.tcenv l)))) datas)) then begin
[]
end else begin
(let _430435 = (fresh_fvar "x" Microsoft_FStar_ToSMT_Term.Term_sort)
in (match (_430435) with
| (xxsym, xx) -> begin
(let _430478 = ((Support.List.fold_left (fun _430438 l -> (match (_430438) with
| (out, decls) -> begin
(let data_t = (Microsoft_FStar_Tc_Env.lookup_datacon env.tcenv l)
in (let _430448 = (match ((Microsoft_FStar_Absyn_Util.function_formals data_t)) with
| Some ((formals, res)) -> begin
(formals, (Microsoft_FStar_Absyn_Util.comp_result res))
end
| None -> begin
([], data_t)
end)
in (match (_430448) with
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
in (let _430466 = (encode_args indices env)
in (match (_430466) with
| (indices, decls') -> begin
(let _430467 = if ((Support.List.length indices) <> (Support.List.length vars)) then begin
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
in (match (_430478) with
| (data_ax, decls) -> begin
(let _430481 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_430481) with
| (ffsym, ff) -> begin
(let xx_has_type = (Microsoft_FStar_ToSMT_Term.mk_HasTypeFuel (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (ff)::[])) xx tapp)
in (Support.List.append decls ((Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((xx_has_type)::[], (add_fuel (ffsym, Microsoft_FStar_ToSMT_Term.Fuel_sort) (((xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))::vars)), (Microsoft_FStar_ToSMT_Term.mkImp (xx_has_type, data_ax)))), Some ("inversion axiom"))))::[])))
end))
end))
end))
end)
in (let k = (Microsoft_FStar_Absyn_Util.close_kind tps k)
in (let _430493 = (match ((Microsoft_FStar_Absyn_Util.compress_kind k).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Kind_arrow ((bs, res)) -> begin
(true, bs, res)
end
| _ -> begin
(false, [], k)
end)
in (match (_430493) with
| (is_kind_arrow, formals, res) -> begin
(let _430500 = (encode_binders None formals env)
in (match (_430500) with
| (vars, guards, env', binder_decls, _) -> begin
(let projection_axioms = (fun tapp vars -> (match (((Support.Microsoft.FStar.Util.find_opt (fun _428349 -> (match (_428349) with
| Microsoft_FStar_Absyn_Syntax.Projector (_) -> begin
true
end
| _ -> begin
false
end))) quals)) with
| Some (Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inl (a)))) -> begin
(let rec projectee = (fun i _428350 -> (match (_428350) with
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
in (let _430539 = (match ((Support.Microsoft.FStar.Util.first_N projectee_pos vars)) with
| (_, xx::suffix) -> begin
(xx, suffix)
end
| _ -> begin
(failwith "impossible")
end)
in (match (_430539) with
| (xx, suffix) -> begin
(let dproj_app = (mk_ApplyT (Microsoft_FStar_ToSMT_Term.mkApp ((mk_typ_projector_name d a), ((Microsoft_FStar_ToSMT_Term.mkFreeV xx))::[])) suffix)
in (Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((tapp)::[], vars, (Microsoft_FStar_ToSMT_Term.mkEq (tapp, dproj_app)))), Some ("projector axiom"))))::[])
end))))
end
| _ -> begin
[]
end))
in (let _430546 = (new_typ_constant_and_tok_from_lid env t)
in (match (_430546) with
| (tname, ttok, env) -> begin
(let ttok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ttok, []))
in (let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let tapp = (Microsoft_FStar_ToSMT_Term.mkApp (tname, (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)))
in (let _430571 = (let tname_decl = (constructor_or_logic_type_decl (tname, ((Support.List.map (fun _430552 -> (match (_430552) with
| (n, s) -> begin
((Support.String.strcat tname n), s)
end))) vars), Microsoft_FStar_ToSMT_Term.Type_sort, (varops.next_id ())))
in (let _430568 = (match (vars) with
| [] -> begin
([], (push_free_tvar env t tname ((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_ToSMT_Term.mkApp (tname, [])))))
end
| _ -> begin
(let ttok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((ttok, [], Microsoft_FStar_ToSMT_Term.Type_sort, Some ("token")))
in (let ttok_fresh = (Microsoft_FStar_ToSMT_Term.fresh_token (ttok, Microsoft_FStar_ToSMT_Term.Type_sort) (varops.next_id ()))
in (let ttok_app = (mk_ApplyT ttok_tm vars)
in (let pats = if ((not (is_logical)) && ((Support.Microsoft.FStar.Util.for_some (fun _428351 -> (match (_428351) with
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
in (match (_430568) with
| (tok_decls, env) -> begin
((Support.List.append tname_decl tok_decls), env)
end)))
in (match (_430571) with
| (decls, env) -> begin
(let kindingAx = (let _430574 = (encode_knd res env' tapp)
in (match (_430574) with
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
(let _430605 = (new_term_constant_and_tok_from_lid env d)
in (match (_430605) with
| (ddconstrsym, ddtok, env) -> begin
(let ddtok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (ddtok, []))
in (let _430614 = (match ((Microsoft_FStar_Absyn_Util.function_formals t)) with
| Some ((f, c)) -> begin
(f, (Microsoft_FStar_Absyn_Util.comp_result c))
end
| None -> begin
([], t)
end)
in (match (_430614) with
| (formals, t_res) -> begin
(let _430617 = (fresh_fvar "f" Microsoft_FStar_ToSMT_Term.Fuel_sort)
in (match (_430617) with
| (fuel_var, fuel_tm) -> begin
(let s_fuel_tm = (Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[]))
in (let _430624 = (encode_binders (Some (fuel_tm)) formals env)
in (match (_430624) with
| (vars, guards, env', binder_decls, names) -> begin
(let projectors = ((Support.List.map (fun _428352 -> (match (_428352) with
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
in (let _430638 = (encode_typ_pred' None t env ddtok_tm)
in (match (_430638) with
| (tok_typing, decls3) -> begin
(let _430645 = (encode_binders (Some (s_fuel_tm)) formals env)
in (match (_430645) with
| (vars', guards', env'', decls_formals, _) -> begin
(let _430650 = (let xvars = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars')
in (let dapp = (Microsoft_FStar_ToSMT_Term.mkApp (ddconstrsym, xvars))
in (encode_typ_pred' (Some (fuel_tm)) t_res env'' dapp)))
in (match (_430650) with
| (ty_pred', decls_pred) -> begin
(let guard' = (Microsoft_FStar_ToSMT_Term.mk_and_l guards')
in (let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| _ -> begin
((Microsoft_FStar_ToSMT_Term.fresh_token (ddtok, Microsoft_FStar_ToSMT_Term.Term_sort) (varops.next_id ())))::[]
end)
in (let encode_elim = (fun _430657 -> (match (_430657) with
| () -> begin
(let _430660 = (Microsoft_FStar_Absyn_Util.head_and_args t_res)
in (match (_430660) with
| (head, args) -> begin
(match ((Microsoft_FStar_Absyn_Util.compress_typ head).Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_const (fv) -> begin
(let encoded_head = (lookup_free_tvar_name env' fv)
in (let _430666 = (encode_args args env')
in (match (_430666) with
| (encoded_args, arg_decls) -> begin
(let _430690 = (Support.List.fold_left (fun _430670 arg -> (match (_430670) with
| (env, arg_vars, eqns) -> begin
(match (arg) with
| Support.Microsoft.FStar.Util.Inl (targ) -> begin
(let _430678 = (gen_typ_var env (Microsoft_FStar_Absyn_Util.new_bvd None))
in (match (_430678) with
| (_, tv, env) -> begin
(env, (tv)::arg_vars, ((Microsoft_FStar_ToSMT_Term.mkEq (targ, tv)))::eqns)
end))
end
| Support.Microsoft.FStar.Util.Inr (varg) -> begin
(let _430685 = (gen_term_var env (Microsoft_FStar_Absyn_Util.new_bvd None))
in (match (_430685) with
| (_, xv, env) -> begin
(env, (xv)::arg_vars, ((Microsoft_FStar_ToSMT_Term.mkEq (varg, xv)))::eqns)
end))
end)
end)) (env', [], []) encoded_args)
in (match (_430690) with
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
(let _430710 = (Microsoft_FStar_Tc_Errors.warn drange (Support.Microsoft.FStar.Util.format2 "Constructor %s builds an unexpected type %s\n" (Microsoft_FStar_Absyn_Print.sli d) (Microsoft_FStar_Absyn_Print.typ_to_string head)))
in ([], []))
end)
end))
end))
in (let _430714 = (encode_elim ())
in (match (_430714) with
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
(let _430727 = (encode_signature env ses)
in (match (_430727) with
| (g, env) -> begin
(let _430739 = ((Support.List.partition (fun _428353 -> (match (_428353) with
| Microsoft_FStar_ToSMT_Term.Assume ((_, Some ("inversion axiom"))) -> begin
false
end
| _ -> begin
true
end))) g)
in (match (_430739) with
| (g', inversions) -> begin
((Support.List.append g' inversions), env)
end))
end))
end
| Microsoft_FStar_Absyn_Syntax.Sig_let (((is_rec, bindings), _, _, quals)) -> begin
(let eta_expand = (fun binders formals body t -> (let nbinders = (Support.List.length binders)
in (let _430758 = (Support.Microsoft.FStar.Util.first_N nbinders formals)
in (match (_430758) with
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
(let _430808 = (Support.Microsoft.FStar.Util.first_N nformals binders)
in (match (_430808) with
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
(let _430817 = (eta_expand binders formals body tres)
in (match (_430817) with
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
in (let _430829 = (eta_expand [] formals e tres)
in (match (_430829) with
| (binders, body) -> begin
(binders, body, formals, tres)
end)))
end
| _ -> begin
([], e, [], t_norm)
end)
end))
in (Support.Prims.try_with (fun _430833 -> (match (_430833) with
| () -> begin
if ((Support.Microsoft.FStar.Util.for_some (fun _428354 -> (match (_428354) with
| Microsoft_FStar_Absyn_Syntax.Opaque -> begin
true
end
| _ -> begin
false
end))) quals) then begin
([], env)
end else begin
if ((Support.Microsoft.FStar.Util.for_some (fun _430855 -> (match (_430855) with
| (_, t, _) -> begin
(Microsoft_FStar_Absyn_Util.is_smt_lemma t)
end))) bindings) then begin
(((Support.List.collect (fun _430860 -> (match (_430860) with
| (flid, t, _) -> begin
if (Microsoft_FStar_Absyn_Util.is_smt_lemma t) then begin
(encode_smt_lemma env (Support.Microsoft.FStar.Util.right flid) t)
end else begin
(raise (Let_rec_unencodeable))
end
end))) bindings), env)
end else begin
(let _430882 = ((Support.List.fold_left (fun _430865 _430870 -> (match ((_430865, _430870)) with
| ((toks, typs, decls, env), (flid, t, _)) -> begin
(let _430871 = if (Microsoft_FStar_Absyn_Util.is_smt_lemma t) then begin
(raise (Let_rec_unencodeable))
end
in (let t_norm = (Microsoft_FStar_Absyn_Util.compress_typ (whnf env t))
in (let _430877 = (declare_top_level_let env (Support.Microsoft.FStar.Util.right flid) t t_norm)
in (match (_430877) with
| (tok, decl, env) -> begin
((((Support.Microsoft.FStar.Util.right flid), tok))::toks, (t_norm)::typs, (decl)::decls, env)
end))))
end)) ([], [], [], env)) bindings)
in (match (_430882) with
| (toks, typs, decls, env) -> begin
(let toks = (Support.List.rev toks)
in (let decls = ((Support.List.flatten) (Support.List.rev decls))
in (let typs = (Support.List.rev typs)
in if (((Support.Microsoft.FStar.Util.for_some (fun _428355 -> (match (_428355) with
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
(let _430911 = (destruct_bound_function flid t_norm e)
in (match (_430911) with
| (binders, body, formals, tres) -> begin
(let _430918 = (encode_binders None binders env)
in (match (_430918) with
| (vars, guards, env', binder_decls, _) -> begin
(let app = (match (vars) with
| [] -> begin
(Microsoft_FStar_ToSMT_Term.mkFreeV (f, Microsoft_FStar_ToSMT_Term.Term_sort))
end
| _ -> begin
(Microsoft_FStar_ToSMT_Term.mkApp (f, (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)))
end)
in (let _430925 = (encode_exp body env')
in (match (_430925) with
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
in (let _430945 = ((Support.List.fold_left (fun _430934 _430939 -> (match ((_430934, _430939)) with
| ((gtoks, env), (flid, (f, ftok))) -> begin
(let g = (varops.new_fvar flid)
in (let gtok = (varops.new_fvar flid)
in (let env = (push_free_var env flid gtok ((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::[]))))
in (((flid, f, ftok, g, gtok))::gtoks, env))))
end)) ([], env)) toks)
in (match (_430945) with
| (gtoks, env) -> begin
(let gtoks = (Support.List.rev gtoks)
in (let encode_one_binding = (fun env0 _430954 t_norm _430961 -> (match ((_430954, _430961)) with
| ((flid, f, ftok, g, gtok), (_, _, e)) -> begin
(let _430966 = (destruct_bound_function flid t_norm e)
in (match (_430966) with
| (binders, body, formals, tres) -> begin
(let _430973 = (encode_binders None binders env)
in (match (_430973) with
| (vars, guards, env', binder_decls, _) -> begin
(let decl_g = Microsoft_FStar_ToSMT_Term.DeclFun ((g, (Microsoft_FStar_ToSMT_Term.Fuel_sort)::(Support.List.map (Support.Prims.snd) vars), Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Fuel-instrumented function name")))
in (let env0 = (push_zfuel_name env0 flid g)
in (let decl_g_tok = Microsoft_FStar_ToSMT_Term.DeclFun ((gtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, Some ("Token for fuel-instrumented partial applications")))
in (let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let app = (Microsoft_FStar_ToSMT_Term.mkApp (f, vars_tm))
in (let gsapp = (Microsoft_FStar_ToSMT_Term.mkApp (g, ((Microsoft_FStar_ToSMT_Term.mkApp ("SFuel", (fuel_tm)::[])))::vars_tm))
in (let gmax = (Microsoft_FStar_ToSMT_Term.mkApp (g, ((Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", [])))::vars_tm))
in (let _430983 = (encode_exp body env')
in (match (_430983) with
| (body_tm, decls2) -> begin
(let eqn_g = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((gsapp)::[], (fuel)::vars, (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l guards), (Microsoft_FStar_ToSMT_Term.mkEq (gsapp, body_tm)))))), Some ((Support.Microsoft.FStar.Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.Microsoft_FStar_Absyn_Syntax.str))))
in (let eqn_f = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((app)::[], vars, (Microsoft_FStar_ToSMT_Term.mkEq (app, gmax)))), Some ("Correspondence of recursive function to instrumented version")))
in (let eqn_g' = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((gsapp)::[], (fuel)::vars, (Microsoft_FStar_ToSMT_Term.mkEq (gsapp, (Microsoft_FStar_ToSMT_Term.mkApp (g, ((Microsoft_FStar_ToSMT_Term.mkFreeV fuel))::vars_tm)))))), Some ("Fuel irrelevance")))
in (let _431006 = (let _430993 = (encode_binders None formals env0)
in (match (_430993) with
| (vars, v_guards, env, binder_decls, _) -> begin
(let vars_tm = (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)
in (let gapp = (Microsoft_FStar_ToSMT_Term.mkApp (g, (fuel_tm)::vars_tm))
in (let tok_corr = (let tok_app = (mk_ApplyE (Microsoft_FStar_ToSMT_Term.mkFreeV (gtok, Microsoft_FStar_ToSMT_Term.Term_sort)) ((fuel)::vars))
in Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((tok_app)::[], (fuel)::vars, (Microsoft_FStar_ToSMT_Term.mkEq (tok_app, gapp)))), Some ("Fuel token correspondence"))))
in (let _431003 = (let _431000 = (encode_typ_pred' None tres env gapp)
in (match (_431000) with
| (g_typing, d3) -> begin
(d3, (Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((gapp)::[], (fuel)::vars, (Microsoft_FStar_ToSMT_Term.mkImp ((Microsoft_FStar_ToSMT_Term.mk_and_l v_guards), g_typing)))), None)))::[])
end))
in (match (_431003) with
| (aux_decls, typing_corr) -> begin
((Support.List.append binder_decls aux_decls), (Support.List.append typing_corr ((tok_corr)::[])))
end)))))
end))
in (match (_431006) with
| (aux_decls, g_typing) -> begin
((Support.List.append (Support.List.append (Support.List.append binder_decls decls2) aux_decls) ((decl_g)::(decl_g_tok)::[])), (Support.List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing), env0)
end)))))
end)))))))))
end))
end))
end))
in (let _431022 = (Support.List.fold_left (fun _431010 _431014 -> (match ((_431010, _431014)) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(let _431018 = (encode_one_binding env0 gtok ty bs)
in (match (_431018) with
| (decls', eqns', env0) -> begin
((decls')::decls, (Support.List.append eqns' eqns), env0)
end))
end)) ((decls)::[], [], env0) (Support.List.zip3 gtoks typs bindings))
in (match (_431022) with
| (decls, eqns, env0) -> begin
(let _431031 = ((Support.List.partition (fun _428356 -> (match (_428356) with
| Microsoft_FStar_ToSMT_Term.DeclFun (_) -> begin
true
end
| _ -> begin
false
end))) ((Support.List.flatten) decls))
in (match (_431031) with
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
end)) (fun _430832 -> (match (_430832) with
| Let_rec_unencodeable -> begin
(let msg = ((Support.String.concat " and ") ((Support.List.map (fun _430841 -> (match (_430841) with
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
(let _431058 = (encode_free_var env x t t_norm [])
in (match (_431058) with
| (decls, env) -> begin
(let _431063 = (lookup_lid env x)
in (match (_431063) with
| (n, x', _) -> begin
((n, x'), decls, env)
end))
end))
end
| Some ((n, x, _)) -> begin
((n, x), [], env)
end))
and encode_smt_lemma = (fun env lid t -> (let _431075 = (encode_function_type_as_formula None t env)
in (match (_431075) with
| (form, decls) -> begin
(Support.List.append decls ((Microsoft_FStar_ToSMT_Term.Assume ((form, Some ((Support.String.strcat "Lemma: " lid.Microsoft_FStar_Absyn_Syntax.str)))))::[]))
end)))
and encode_free_var = (fun env lid tt t_norm quals -> if ((not ((Microsoft_FStar_Absyn_Util.is_pure_or_ghost_function t_norm))) || (Microsoft_FStar_Absyn_Util.is_lemma t_norm)) then begin
(let _431084 = (new_term_constant_and_tok_from_lid env lid)
in (match (_431084) with
| (vname, vtok, env) -> begin
(let arg_sorts = (match (t_norm.Microsoft_FStar_Absyn_Syntax.n) with
| Microsoft_FStar_Absyn_Syntax.Typ_fun ((binders, _)) -> begin
((Support.List.map (fun _428357 -> (match (_428357) with
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
(let _431114 = (match ((Microsoft_FStar_Absyn_Util.function_formals t_norm)) with
| Some ((args, comp)) -> begin
(args, (Microsoft_FStar_Absyn_Util.comp_result comp))
end
| None -> begin
([], t_norm)
end)
in (match (_431114) with
| (formals, res) -> begin
(let _431118 = (new_term_constant_and_tok_from_lid env lid)
in (match (_431118) with
| (vname, vtok, env) -> begin
(let vtok_tm = (Microsoft_FStar_ToSMT_Term.mkApp (vtok, []))
in (let mk_disc_proj_axioms = (fun vapp vars -> ((Support.List.collect (fun _428358 -> (match (_428358) with
| Microsoft_FStar_Absyn_Syntax.Discriminator (d) -> begin
(let _431132 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_431132) with
| (_, (xxsym, _)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((vapp)::[], vars, (Microsoft_FStar_ToSMT_Term.mkEq (vapp, (Microsoft_FStar_ToSMT_Term.boxBool (Microsoft_FStar_ToSMT_Term.mk_tester (escape d.Microsoft_FStar_Absyn_Syntax.str) xx)))))), None)))::[])
end))
end
| Microsoft_FStar_Absyn_Syntax.Projector ((d, Support.Microsoft.FStar.Util.Inr (f))) -> begin
(let _431145 = (Support.Microsoft.FStar.Util.prefix vars)
in (match (_431145) with
| (_, (xxsym, _)) -> begin
(let xx = (Microsoft_FStar_ToSMT_Term.mkFreeV (xxsym, Microsoft_FStar_ToSMT_Term.Term_sort))
in (Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((vapp)::[], vars, (Microsoft_FStar_ToSMT_Term.mkEq (vapp, (Microsoft_FStar_ToSMT_Term.mkApp ((mk_term_projector_name d f), (xx)::[])))))), None)))::[])
end))
end
| _ -> begin
[]
end))) quals))
in (let _431155 = (encode_binders None formals env)
in (match (_431155) with
| (vars, guards, env', decls1, _) -> begin
(let guard = (Microsoft_FStar_ToSMT_Term.mk_and_l guards)
in (let vtok_app = (mk_ApplyE vtok_tm vars)
in (let vapp = (Microsoft_FStar_ToSMT_Term.mkApp (vname, (Support.List.map Microsoft_FStar_ToSMT_Term.mkFreeV vars)))
in (let _431188 = (let vname_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((vname, ((Support.List.map (fun _428359 -> (match (_428359) with
| (Support.Microsoft.FStar.Util.Inl (_), _) -> begin
Microsoft_FStar_ToSMT_Term.Type_sort
end
| _ -> begin
Microsoft_FStar_ToSMT_Term.Term_sort
end))) formals), Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let _431185 = (match (formals) with
| [] -> begin
(let _431172 = if (not ((head_normal env tt))) then begin
(encode_typ_pred' None tt env (Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort)))
end else begin
(encode_typ_pred' None t_norm env (Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort)))
end
in (match (_431172) with
| (t, decls2) -> begin
(let tok_typing = Microsoft_FStar_ToSMT_Term.Assume ((t, Some ("function token typing")))
in ((Support.List.append decls2 ((tok_typing)::[])), (push_free_var env lid vname ((fun __dataconst_1 -> Some (__dataconst_1)) (Microsoft_FStar_ToSMT_Term.mkFreeV (vname, Microsoft_FStar_ToSMT_Term.Term_sort))))))
end))
end
| _ -> begin
(let vtok_decl = Microsoft_FStar_ToSMT_Term.DeclFun ((vtok, [], Microsoft_FStar_ToSMT_Term.Term_sort, None))
in (let vtok_fresh = (Microsoft_FStar_ToSMT_Term.fresh_token (vtok, Microsoft_FStar_ToSMT_Term.Term_sort) (varops.next_id ()))
in (let name_tok_corr = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkForall ((vtok_app)::[], vars, (Microsoft_FStar_ToSMT_Term.mkEq (vtok_app, vapp)))), None))
in (let _431181 = if (not ((head_normal env tt))) then begin
(encode_typ_pred' None tt env vtok_tm)
end else begin
(encode_typ_pred' None t_norm env vtok_tm)
end
in (match (_431181) with
| (tok_typing, decls2) -> begin
(let tok_typing = Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, Some ("function token typing")))
in ((Support.List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[])), env))
end)))))
end)
in (match (_431185) with
| (tok_decl, env) -> begin
((vname_decl)::tok_decl, env)
end)))
in (match (_431188) with
| (decls2, env) -> begin
(let _431191 = (encode_typ_pred' None res env' vapp)
in (match (_431191) with
| (ty_pred, decls3) -> begin
(let _431197 = if (not ((head_normal env tt))) then begin
(let _431194 = (encode_typ_pred' None tt env vtok_tm)
in (match (_431194) with
| (tok_typing, decls4) -> begin
((Microsoft_FStar_ToSMT_Term.Assume ((tok_typing, None)))::[], decls4)
end))
end else begin
([], [])
end
in (match (_431197) with
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
and encode_signature = (fun env ses -> ((Support.List.fold_left (fun _431204 se -> (match (_431204) with
| (g, env) -> begin
(let _431208 = (encode_sigelt env se)
in (match (_431208) with
| (g', env) -> begin
((Support.List.append g g'), env)
end))
end)) ([], env)) ses))

let encode_env_bindings = (fun env bindings -> (let encode_binding = (fun b _431215 -> (match (_431215) with
| (decls, env) -> begin
(match (b) with
| Microsoft_FStar_Tc_Env.Binding_var ((x, t0)) -> begin
(let _431223 = (new_term_constant env x)
in (match (_431223) with
| (xxsym, xx, env') -> begin
(let t1 = (norm_t env t0)
in (let _431227 = (encode_typ_pred' None t1 env xx)
in (match (_431227) with
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
(let _431237 = (new_typ_constant env a)
in (match (_431237) with
| (aasym, aa, env') -> begin
(let _431240 = (encode_knd k env aa)
in (match (_431240) with
| (k, decls') -> begin
(let g = (Support.List.append (Support.List.append ((Microsoft_FStar_ToSMT_Term.DeclFun ((aasym, [], Microsoft_FStar_ToSMT_Term.Type_sort, Some ((Microsoft_FStar_Absyn_Print.strBvd a)))))::[]) decls') ((Microsoft_FStar_ToSMT_Term.Assume ((k, None)))::[]))
in ((Support.List.append decls g), env'))
end))
end))
end
| Microsoft_FStar_Tc_Env.Binding_lid ((x, t)) -> begin
(let t_norm = (whnf env t)
in (let _431249 = (encode_free_var env x t t_norm [])
in (match (_431249) with
| (g, env') -> begin
((Support.List.append decls g), env')
end)))
end
| Microsoft_FStar_Tc_Env.Binding_sig (se) -> begin
(let _431254 = (encode_sigelt env se)
in (match (_431254) with
| (g, env') -> begin
((Support.List.append decls g), env')
end))
end)
end))
in (Support.List.fold_right encode_binding bindings ([], env))))

let encode_labels = (fun labs -> (let prefix = ((Support.List.map (fun _431261 -> (match (_431261) with
| (l, _, _) -> begin
Microsoft_FStar_ToSMT_Term.DeclFun (((Support.Prims.fst l), [], Microsoft_FStar_ToSMT_Term.Bool_sort, None))
end))) labs)
in (let suffix = ((Support.List.collect (fun _431268 -> (match (_431268) with
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
(let _431277 = e
in {bindings = _431277.bindings; depth = _431277.depth; tcenv = tcenv; warn = _431277.warn; cache = _431277.cache; nolabels = _431277.nolabels; use_zfuel_name = _431277.use_zfuel_name})
end))

let set_env = (fun env -> (match ((! (last_env))) with
| [] -> begin
(failwith "Empty env stack")
end
| _::tl -> begin
(last_env := (env)::tl)
end))

let push_env = (fun _431285 -> (match (_431285) with
| () -> begin
(match ((! (last_env))) with
| [] -> begin
(failwith "Empty env stack")
end
| hd::tl -> begin
(let _431290 = (Microsoft_FStar_ToSMT_Term.push ())
in (let refs = (Support.Microsoft.FStar.Util.smap_copy hd.cache)
in (let top = (let _431293 = hd
in {bindings = _431293.bindings; depth = _431293.depth; tcenv = _431293.tcenv; warn = _431293.warn; cache = refs; nolabels = _431293.nolabels; use_zfuel_name = _431293.use_zfuel_name})
in (last_env := (top)::(hd)::tl))))
end)
end))

let pop_env = (fun _431296 -> (match (_431296) with
| () -> begin
(match ((! (last_env))) with
| [] -> begin
(failwith "Popping an empty stack")
end
| _::tl -> begin
(let _431302 = (Microsoft_FStar_ToSMT_Term.pop ())
in (last_env := tl))
end)
end))

let mark_env = (fun _431304 -> (match (_431304) with
| () -> begin
(push_env ())
end))

let reset_mark_env = (fun _431305 -> (match (_431305) with
| () -> begin
(pop_env ())
end))

let commit_mark_env = (fun _431306 -> (match (_431306) with
| () -> begin
(let _431307 = (Microsoft_FStar_ToSMT_Term.commit_mark ())
in (match ((! (last_env))) with
| hd::_::tl -> begin
(last_env := (hd)::tl)
end
| _ -> begin
(failwith "Impossible")
end))
end))

let init = (fun tcenv -> (let _431318 = (init_env tcenv)
in (let _431320 = (Microsoft_FStar_ToSMT_Z3.init ())
in (Microsoft_FStar_ToSMT_Z3.giveZ3 ((Microsoft_FStar_ToSMT_Term.DefPrelude)::[])))))

let push = (fun msg -> (let _431323 = (push_env ())
in (let _431325 = (varops.push ())
in (Microsoft_FStar_ToSMT_Z3.push msg))))

let pop = (fun msg -> (let _431328 = ((Support.Prims.ignore) (pop_env ()))
in (let _431330 = (varops.pop ())
in (Microsoft_FStar_ToSMT_Z3.pop msg))))

let mark = (fun msg -> (let _431333 = (mark_env ())
in (let _431335 = (varops.mark ())
in (Microsoft_FStar_ToSMT_Z3.mark msg))))

let reset_mark = (fun msg -> (let _431338 = (reset_mark_env ())
in (let _431340 = (varops.reset_mark ())
in (Microsoft_FStar_ToSMT_Z3.reset_mark msg))))

let commit_mark = (fun msg -> (let _431343 = (commit_mark_env ())
in (let _431345 = (varops.commit_mark ())
in (Microsoft_FStar_ToSMT_Z3.commit_mark msg))))

let encode_sig = (fun tcenv se -> (let caption = (fun decls -> if (! (Microsoft_FStar_Options.logQueries)) then begin
(Microsoft_FStar_ToSMT_Term.Caption ((Support.String.strcat "encoding sigelt " (Microsoft_FStar_Absyn_Print.sigelt_to_string_short se))))::decls
end else begin
decls
end)
in (let env = (get_env tcenv)
in (let _431354 = (encode_sigelt env se)
in (match (_431354) with
| (decls, env) -> begin
(let _431355 = (set_env env)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 (caption decls)))
end)))))

let encode_modul = (fun tcenv modul -> (let name = (Support.Microsoft.FStar.Util.format2 "%s %s" (if modul.Microsoft_FStar_Absyn_Syntax.is_interface then begin
"interface"
end else begin
"module"
end) modul.Microsoft_FStar_Absyn_Syntax.name.Microsoft_FStar_Absyn_Syntax.str)
in (let _431360 = if (Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint2 "Encoding externals for %s ... %s exports\n" name (Support.Microsoft.FStar.Util.string_of_int (Support.List.length modul.Microsoft_FStar_Absyn_Syntax.exports)))
end
in (let env = (get_env tcenv)
in (let _431367 = (encode_signature (let _431363 = env
in {bindings = _431363.bindings; depth = _431363.depth; tcenv = _431363.tcenv; warn = false; cache = _431363.cache; nolabels = _431363.nolabels; use_zfuel_name = _431363.use_zfuel_name}) modul.Microsoft_FStar_Absyn_Syntax.exports)
in (match (_431367) with
| (decls, env) -> begin
(let caption = (fun decls -> if (! (Microsoft_FStar_Options.logQueries)) then begin
(let msg = (Support.String.strcat "Externals for " name)
in (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::decls) ((Microsoft_FStar_ToSMT_Term.Caption ((Support.String.strcat "End " msg)))::[])))
end else begin
decls
end)
in (let _431373 = (set_env (let _431371 = env
in {bindings = _431371.bindings; depth = _431371.depth; tcenv = _431371.tcenv; warn = true; cache = _431371.cache; nolabels = _431371.nolabels; use_zfuel_name = _431371.use_zfuel_name}))
in (let _431375 = if (Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint1 "Done encoding externals for %s\n" name)
end
in (let decls = (caption decls)
in (Microsoft_FStar_ToSMT_Z3.giveZ3 decls)))))
end))))))

let solve = (fun tcenv q -> (let _431380 = (push (Support.Microsoft.FStar.Util.format1 "Starting query at %s" (Support.Microsoft.FStar.Range.string_of_range (Microsoft_FStar_Tc_Env.get_range tcenv))))
in (let pop = (fun _431383 -> (match (_431383) with
| () -> begin
(pop (Support.Microsoft.FStar.Util.format1 "Ending query at %s" (Support.Microsoft.FStar.Range.string_of_range (Microsoft_FStar_Tc_Env.get_range tcenv))))
end))
in (let _431413 = (let env = (get_env tcenv)
in (let bindings = (Microsoft_FStar_Tc_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (let _431396 = (encode_env_bindings env (Support.List.filter (fun _428360 -> (match (_428360) with
| Microsoft_FStar_Tc_Env.Binding_sig (_) -> begin
false
end
| _ -> begin
true
end)) bindings))
in (match (_431396) with
| (env_decls, env) -> begin
(let _431397 = if (Microsoft_FStar_Tc_Env.debug tcenv Microsoft_FStar_Options.Low) then begin
(Support.Microsoft.FStar.Util.fprint1 "Encoding query formula: %s\n" (Microsoft_FStar_Absyn_Print.formula_to_string q))
end
in (let _431402 = (encode_formula_with_labels q env)
in (match (_431402) with
| (phi, labels, qdecls) -> begin
(let _431405 = (encode_labels labels)
in (match (_431405) with
| (label_prefix, label_suffix) -> begin
(let query_prelude = (Support.List.append (Support.List.append env_decls label_prefix) qdecls)
in (let qry = Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkNot phi), Some ("query")))
in (let suffix = (Support.List.append label_suffix ((Microsoft_FStar_ToSMT_Term.Echo ("Done!"))::[]))
in (query_prelude, labels, qry, suffix))))
end))
end)))
end))))
in (match (_431413) with
| (prefix, labels, qry, suffix) -> begin
(match (qry) with
| Microsoft_FStar_ToSMT_Term.Assume (({Microsoft_FStar_ToSMT_Term.tm = Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.False, _)); Microsoft_FStar_ToSMT_Term.hash = _; Microsoft_FStar_ToSMT_Term.freevars = _}, _)) -> begin
(let _431428 = (pop ())
in ())
end
| _ when tcenv.Microsoft_FStar_Tc_Env.admit -> begin
(let _431432 = (pop ())
in ())
end
| Microsoft_FStar_ToSMT_Term.Assume ((q, _)) -> begin
(let fresh = ((Support.String.length q.Microsoft_FStar_ToSMT_Term.hash) >= 2048)
in (let _431440 = (Microsoft_FStar_ToSMT_Z3.giveZ3 prefix)
in (let with_fuel = (fun _431445 -> (match (_431445) with
| (n, i) -> begin
(Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption ((Support.Microsoft.FStar.Util.format1 "<fuel=\'%s\'>" (Support.Microsoft.FStar.Util.string_of_int n))))::(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkEq ((Microsoft_FStar_ToSMT_Term.mkApp ("MaxFuel", [])), (Microsoft_FStar_ToSMT_Term.n_fuel n))), None)))::(Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkEq ((Microsoft_FStar_ToSMT_Term.mkApp ("MaxIFuel", [])), (Microsoft_FStar_ToSMT_Term.n_fuel i))), None)))::(qry)::(Microsoft_FStar_ToSMT_Term.CheckSat)::[]) suffix)
end))
in (let check = (fun _431447 -> (match (_431447) with
| () -> begin
(let initial_config = ((! (Microsoft_FStar_Options.initial_fuel)), (! (Microsoft_FStar_Options.initial_ifuel)))
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
in (let report = (fun _431453 -> (match (_431453) with
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
in (let rec try_alt_configs = (fun errs _428361 -> (match (_428361) with
| [] -> begin
(report (false, errs))
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(Microsoft_FStar_ToSMT_Z3.ask fresh labels (with_fuel mi) (cb []))
end
| _ -> begin
(report (false, errs))
end)
end
| mi::tl -> begin
(Microsoft_FStar_ToSMT_Z3.ask fresh labels (with_fuel mi) (fun _431473 -> (match (_431473) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb tl (ok, errs'))
end
| _ -> begin
(cb tl (ok, errs))
end)
end)))
end))
and cb = (fun alt _431480 -> (match (_431480) with
| (ok, errs) -> begin
if ok then begin
()
end else begin
(try_alt_configs errs alt)
end
end))
in (Microsoft_FStar_ToSMT_Z3.ask fresh labels (with_fuel initial_config) (cb alt_configs))))))
end))
in (let _431481 = if (! (Microsoft_FStar_Options.admit_smt_queries)) then begin
()
end else begin
(check ())
end
in (pop ()))))))
end)
end)))))

let is_trivial = (fun tcenv q -> (let env = (get_env tcenv)
in (let _431486 = (push "query")
in (let _431493 = (encode_formula_with_labels q env)
in (match (_431493) with
| (f, _, _) -> begin
(let _431494 = (pop "query")
in (match (f.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.True, _)) -> begin
true
end
| _ -> begin
false
end))
end)))))

let solver = {Microsoft_FStar_Tc_Env.init = init; Microsoft_FStar_Tc_Env.push = push; Microsoft_FStar_Tc_Env.pop = pop; Microsoft_FStar_Tc_Env.mark = mark; Microsoft_FStar_Tc_Env.reset_mark = reset_mark; Microsoft_FStar_Tc_Env.commit_mark = (commit_mark); Microsoft_FStar_Tc_Env.encode_modul = encode_modul; Microsoft_FStar_Tc_Env.encode_sig = encode_sig; Microsoft_FStar_Tc_Env.solve = solve; Microsoft_FStar_Tc_Env.is_trivial = is_trivial; Microsoft_FStar_Tc_Env.finish = Microsoft_FStar_ToSMT_Z3.finish; Microsoft_FStar_Tc_Env.refresh = Microsoft_FStar_ToSMT_Z3.refresh}

let dummy = {Microsoft_FStar_Tc_Env.init = (fun _431503 -> ()); Microsoft_FStar_Tc_Env.push = (fun _431505 -> ()); Microsoft_FStar_Tc_Env.pop = (fun _431507 -> ()); Microsoft_FStar_Tc_Env.mark = (fun _431509 -> ()); Microsoft_FStar_Tc_Env.reset_mark = (fun _431511 -> ()); Microsoft_FStar_Tc_Env.commit_mark = (fun _431513 -> ()); Microsoft_FStar_Tc_Env.encode_modul = (fun _431515 _431517 -> ()); Microsoft_FStar_Tc_Env.encode_sig = (fun _431519 _431521 -> ()); Microsoft_FStar_Tc_Env.solve = (fun _431523 _431525 -> ()); Microsoft_FStar_Tc_Env.is_trivial = (fun _431527 _431529 -> false); Microsoft_FStar_Tc_Env.finish = (fun _431531 -> (match (_431531) with
| () -> begin
()
end)); Microsoft_FStar_Tc_Env.refresh = (fun _431532 -> (match (_431532) with
| () -> begin
()
end))}






open Prims
open FStar_Pervasives
exception Inner_let_rec of ((Prims.string * FStar_Range.range) Prims.list)


let uu___is_Inner_let_rec : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inner_let_rec (uu____46) -> begin
true
end
| uu____55 -> begin
false
end))


let __proj__Inner_let_rec__item__uu___ : Prims.exn  ->  (Prims.string * FStar_Range.range) Prims.list = (fun projectee -> (match (projectee) with
| Inner_let_rec (uu____77) -> begin
uu____77
end))


let add_fuel : 'Auu____92 . 'Auu____92  ->  'Auu____92 Prims.list  ->  'Auu____92 Prims.list = (fun x tl1 -> (

let uu____109 = (FStar_Options.unthrottle_inductives ())
in (match (uu____109) with
| true -> begin
tl1
end
| uu____114 -> begin
(x)::tl1
end)))


let withenv : 'Auu____127 'Auu____128 'Auu____129 . 'Auu____127  ->  ('Auu____128 * 'Auu____129)  ->  ('Auu____128 * 'Auu____129 * 'Auu____127) = (fun c uu____149 -> (match (uu____149) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs : 'Auu____165 'Auu____166 'Auu____167 . (('Auu____165, 'Auu____166) FStar_Util.either * 'Auu____167) Prims.list  ->  (('Auu____165, 'Auu____166) FStar_Util.either * 'Auu____167) Prims.list = (fun args -> (FStar_List.filter (fun uu___0_214 -> (match (uu___0_214) with
| (FStar_Util.Inl (uu____224), uu____225) -> begin
false
end
| uu____231 -> begin
true
end)) args))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s 39 (*'*) 95 (*_*)))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let uu____264 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape uu____264)))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail1 = (fun uu____294 -> (

let uu____295 = (FStar_Util.format2 "Projector %s on data constructor %s not found" (Prims.string_of_int i) lid.FStar_Ident.str)
in (failwith uu____295)))
in (

let uu____299 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (uu____299) with
| (uu____305, t) -> begin
(

let uu____307 = (

let uu____308 = (FStar_Syntax_Subst.compress t)
in uu____308.FStar_Syntax_Syntax.n)
in (match (uu____307) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____334 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____334) with
| (binders, uu____341) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail1 ())
end
| uu____351 -> begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (FStar_Pervasives_Native.fst b)))
end)
end))
end
| uu____368 -> begin
(fail1 ())
end))
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (

let uu____383 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (Prims.string_of_int i))
in (FStar_All.pipe_left escape uu____383)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (

let uu____399 = (

let uu____400 = (

let uu____406 = (mk_term_projector_name lid a)
in ((uu____406), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Term.mk_fv uu____400))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____399)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (

let uu____422 = (

let uu____423 = (

let uu____429 = (mk_term_projector_name_by_pos lid i)
in ((uu____429), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Term.mk_fv uu____423))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____422)))


let mk_data_tester : 'Auu____441 . 'Auu____441  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

type varops_t =
{push : unit  ->  unit; pop : unit  ->  unit; snapshot : unit  ->  (Prims.int * unit); rollback : Prims.int FStar_Pervasives_Native.option  ->  unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string  ->  Prims.string; reset_fresh : unit  ->  unit; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let __proj__Mkvarops_t__item__push : varops_t  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; reset_fresh = reset_fresh; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
push1
end))


let __proj__Mkvarops_t__item__pop : varops_t  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; reset_fresh = reset_fresh; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
pop1
end))


let __proj__Mkvarops_t__item__snapshot : varops_t  ->  unit  ->  (Prims.int * unit) = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; reset_fresh = reset_fresh; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
snapshot1
end))


let __proj__Mkvarops_t__item__rollback : varops_t  ->  Prims.int FStar_Pervasives_Native.option  ->  unit = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; reset_fresh = reset_fresh; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
rollback1
end))


let __proj__Mkvarops_t__item__new_var : varops_t  ->  FStar_Ident.ident  ->  Prims.int  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; reset_fresh = reset_fresh; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
new_var
end))


let __proj__Mkvarops_t__item__new_fvar : varops_t  ->  FStar_Ident.lident  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; reset_fresh = reset_fresh; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
new_fvar
end))


let __proj__Mkvarops_t__item__fresh : varops_t  ->  Prims.string  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; reset_fresh = reset_fresh; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
fresh1
end))


let __proj__Mkvarops_t__item__reset_fresh : varops_t  ->  unit  ->  unit = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; reset_fresh = reset_fresh; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
reset_fresh
end))


let __proj__Mkvarops_t__item__string_const : varops_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; reset_fresh = reset_fresh; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
string_const
end))


let __proj__Mkvarops_t__item__next_id : varops_t  ->  unit  ->  Prims.int = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; reset_fresh = reset_fresh; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
next_id1
end))


let __proj__Mkvarops_t__item__mk_unique : varops_t  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; reset_fresh = reset_fresh; string_const = string_const; next_id = next_id1; mk_unique = mk_unique} -> begin
mk_unique
end))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun uu____1559 -> (

let uu____1560 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____1566 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((uu____1560), (uu____1566)))))
in (

let scopes = (

let uu____1589 = (

let uu____1601 = (new_scope ())
in (uu____1601)::[])
in (FStar_Util.mk_ref uu____1589))
in (

let mk_unique = (fun y -> (

let y1 = (escape y)
in (

let y2 = (

let uu____1653 = (

let uu____1657 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____1657 (fun uu____1723 -> (match (uu____1723) with
| (names1, uu____1737) -> begin
(FStar_Util.smap_try_find names1 y1)
end))))
in (match (uu____1653) with
| FStar_Pervasives_Native.None -> begin
y1
end
| FStar_Pervasives_Native.Some (uu____1751) -> begin
((FStar_Util.incr ctr);
(

let uu____1755 = (

let uu____1757 = (

let uu____1759 = (FStar_ST.op_Bang ctr)
in (Prims.string_of_int uu____1759))
in (Prims.op_Hat "__" uu____1757))
in (Prims.op_Hat y1 uu____1755));
)
end))
in (

let top_scope = (

let uu____1787 = (

let uu____1797 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1797))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1787))
in ((FStar_Util.smap_add top_scope y2 true);
y2;
)))))
in (

let new_var = (fun pp rn -> (FStar_All.pipe_left mk_unique (Prims.op_Hat pp.FStar_Ident.idText (Prims.op_Hat "__" (Prims.string_of_int rn)))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id1 = (fun uu____1909 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
))
in (

let fresh1 = (fun mname pfx -> (

let uu____1948 = (

let uu____1950 = (next_id1 ())
in (FStar_All.pipe_left Prims.string_of_int uu____1950))
in (FStar_Util.format3 "%s_%s_%s" pfx mname uu____1948)))
in (

let reset_fresh = (fun uu____1960 -> (FStar_ST.op_Colon_Equals ctr initial_ctr))
in (

let string_const = (fun s -> (

let uu____1990 = (

let uu____1993 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____1993 (fun uu____2058 -> (match (uu____2058) with
| (uu____2070, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____1990) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let id1 = (next_id1 ())
in (

let f = (

let uu____2086 = (FStar_SMTEncoding_Util.mk_String_const id1)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____2086))
in (

let top_scope = (

let uu____2090 = (

let uu____2100 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____2100))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____2090))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push1 = (fun uu____2184 -> (

let uu____2185 = (

let uu____2197 = (new_scope ())
in (

let uu____2207 = (FStar_ST.op_Bang scopes)
in (uu____2197)::uu____2207))
in (FStar_ST.op_Colon_Equals scopes uu____2185)))
in (

let pop1 = (fun uu____2315 -> (

let uu____2316 = (

let uu____2328 = (FStar_ST.op_Bang scopes)
in (FStar_List.tl uu____2328))
in (FStar_ST.op_Colon_Equals scopes uu____2316)))
in (

let snapshot1 = (fun uu____2441 -> (FStar_Common.snapshot push1 scopes ()))
in (

let rollback1 = (fun depth -> (FStar_Common.rollback pop1 scopes depth))
in {push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; reset_fresh = reset_fresh; string_const = string_const; next_id = next_id1; mk_unique = mk_unique})))))))))))))))

type fvar_binding =
{fvar_lid : FStar_Ident.lident; smt_arity : Prims.int; smt_id : Prims.string; smt_token : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option; smt_fuel_partial_app : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option; fvb_thunked : Prims.bool}


let __proj__Mkfvar_binding__item__fvar_lid : fvar_binding  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app; fvb_thunked = fvb_thunked} -> begin
fvar_lid
end))


let __proj__Mkfvar_binding__item__smt_arity : fvar_binding  ->  Prims.int = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app; fvb_thunked = fvb_thunked} -> begin
smt_arity
end))


let __proj__Mkfvar_binding__item__smt_id : fvar_binding  ->  Prims.string = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app; fvb_thunked = fvb_thunked} -> begin
smt_id
end))


let __proj__Mkfvar_binding__item__smt_token : fvar_binding  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app; fvb_thunked = fvb_thunked} -> begin
smt_token
end))


let __proj__Mkfvar_binding__item__smt_fuel_partial_app : fvar_binding  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app; fvb_thunked = fvb_thunked} -> begin
smt_fuel_partial_app
end))


let __proj__Mkfvar_binding__item__fvb_thunked : fvar_binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {fvar_lid = fvar_lid; smt_arity = smt_arity; smt_id = smt_id; smt_token = smt_token; smt_fuel_partial_app = smt_fuel_partial_app; fvb_thunked = fvb_thunked} -> begin
fvb_thunked
end))


let fvb_to_string : fvar_binding  ->  Prims.string = (fun fvb -> (

let term_opt_to_string = (fun uu___1_2652 -> (match (uu___1_2652) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (s) -> begin
(FStar_SMTEncoding_Term.print_smt_term s)
end))
in (

let uu____2658 = (FStar_Ident.string_of_lid fvb.fvar_lid)
in (

let uu____2660 = (term_opt_to_string fvb.smt_token)
in (

let uu____2662 = (term_opt_to_string fvb.smt_fuel_partial_app)
in (

let uu____2664 = (FStar_Util.string_of_bool fvb.fvb_thunked)
in (FStar_Util.format5 "{ lid = %s;\n  smt_id = %s;\n  smt_token = %s;\n smt_fuel_partial_app = %s;\n fvb_thunked = %s }" uu____2658 fvb.smt_id uu____2660 uu____2662 uu____2664)))))))


let check_valid_fvb : fvar_binding  ->  unit = (fun fvb -> ((match ((((FStar_Option.isSome fvb.smt_token) || (FStar_Option.isSome fvb.smt_fuel_partial_app)) && fvb.fvb_thunked)) with
| true -> begin
(

let uu____2675 = (

let uu____2677 = (FStar_Ident.string_of_lid fvb.fvar_lid)
in (FStar_Util.format1 "Unexpected thunked SMT symbol: %s" uu____2677))
in (failwith uu____2675))
end
| uu____2680 -> begin
(match ((fvb.fvb_thunked && (Prims.op_disEquality fvb.smt_arity (Prims.parse_int "0")))) with
| true -> begin
(

let uu____2685 = (

let uu____2687 = (FStar_Ident.string_of_lid fvb.fvar_lid)
in (FStar_Util.format1 "Unexpected arity of thunked SMT symbol: %s" uu____2687))
in (failwith uu____2685))
end
| uu____2690 -> begin
()
end)
end);
(match (fvb.smt_token) with
| FStar_Pervasives_Native.Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (uu____2692); FStar_SMTEncoding_Term.freevars = uu____2693; FStar_SMTEncoding_Term.rng = uu____2694}) -> begin
(

let uu____2715 = (

let uu____2717 = (fvb_to_string fvb)
in (FStar_Util.format1 "bad fvb\n%s" uu____2717))
in (failwith uu____2715))
end
| uu____2720 -> begin
()
end);
))


let binder_of_eithervar : 'Auu____2730 'Auu____2731 . 'Auu____2730  ->  ('Auu____2730 * 'Auu____2731 FStar_Pervasives_Native.option) = (fun v1 -> ((v1), (FStar_Pervasives_Native.None)))

type env_t =
{bvar_bindings : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap FStar_Util.psmap; fvar_bindings : (fvar_binding FStar_Util.psmap * fvar_binding Prims.list); depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool; current_module_name : Prims.string; encoding_quantifier : Prims.bool; global_cache : FStar_SMTEncoding_Term.decls_elt FStar_Util.smap}


let __proj__Mkenv_t__item__bvar_bindings : env_t  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap FStar_Util.psmap = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier; global_cache = global_cache} -> begin
bvar_bindings
end))


let __proj__Mkenv_t__item__fvar_bindings : env_t  ->  (fvar_binding FStar_Util.psmap * fvar_binding Prims.list) = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier; global_cache = global_cache} -> begin
fvar_bindings
end))


let __proj__Mkenv_t__item__depth : env_t  ->  Prims.int = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier; global_cache = global_cache} -> begin
depth
end))


let __proj__Mkenv_t__item__tcenv : env_t  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier; global_cache = global_cache} -> begin
tcenv
end))


let __proj__Mkenv_t__item__warn : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier; global_cache = global_cache} -> begin
warn
end))


let __proj__Mkenv_t__item__nolabels : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier; global_cache = global_cache} -> begin
nolabels
end))


let __proj__Mkenv_t__item__use_zfuel_name : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier; global_cache = global_cache} -> begin
use_zfuel_name
end))


let __proj__Mkenv_t__item__encode_non_total_function_typ : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier; global_cache = global_cache} -> begin
encode_non_total_function_typ
end))


let __proj__Mkenv_t__item__current_module_name : env_t  ->  Prims.string = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier; global_cache = global_cache} -> begin
current_module_name
end))


let __proj__Mkenv_t__item__encoding_quantifier : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier; global_cache = global_cache} -> begin
encoding_quantifier
end))


let __proj__Mkenv_t__item__global_cache : env_t  ->  FStar_SMTEncoding_Term.decls_elt FStar_Util.smap = (fun projectee -> (match (projectee) with
| {bvar_bindings = bvar_bindings; fvar_bindings = fvar_bindings; depth = depth; tcenv = tcenv; warn = warn; nolabels = nolabels; use_zfuel_name = use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = current_module_name; encoding_quantifier = encoding_quantifier; global_cache = global_cache} -> begin
global_cache
end))


let print_env : env_t  ->  Prims.string = (fun e -> (

let bvars = (FStar_Util.psmap_fold e.bvar_bindings (fun _k pi acc -> (FStar_Util.pimap_fold pi (fun _i uu____3387 acc1 -> (match (uu____3387) with
| (x, _term) -> begin
(

let uu____3402 = (FStar_Syntax_Print.bv_to_string x)
in (uu____3402)::acc1)
end)) acc)) [])
in (

let allvars = (

let uu____3409 = (FStar_All.pipe_right e.fvar_bindings FStar_Pervasives_Native.fst)
in (FStar_Util.psmap_fold uu____3409 (fun _k fvb acc -> (fvb.fvar_lid)::acc) []))
in (

let last_fvar = (match ((FStar_List.rev allvars)) with
| [] -> begin
""
end
| (l)::uu____3442 -> begin
(

let uu____3445 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.op_Hat "...," uu____3445))
end)
in (FStar_String.concat ", " ((last_fvar)::bvars))))))


let lookup_bvar_binding : env_t  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.option = (fun env bv -> (

let uu____3467 = (FStar_Util.psmap_try_find env.bvar_bindings bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (match (uu____3467) with
| FStar_Pervasives_Native.Some (bvs) -> begin
(FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index)
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end)))


let lookup_fvar_binding : env_t  ->  FStar_Ident.lident  ->  fvar_binding FStar_Pervasives_Native.option = (fun env lid -> (

let uu____3528 = (FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst)
in (FStar_Util.psmap_try_find uu____3528 lid.FStar_Ident.str)))


let add_bvar_binding : 'Auu____3552 . (FStar_Syntax_Syntax.bv * 'Auu____3552)  ->  (FStar_Syntax_Syntax.bv * 'Auu____3552) FStar_Util.pimap FStar_Util.psmap  ->  (FStar_Syntax_Syntax.bv * 'Auu____3552) FStar_Util.pimap FStar_Util.psmap = (fun bvb bvbs -> (FStar_Util.psmap_modify bvbs (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname.FStar_Ident.idText (fun pimap_opt -> (

let uu____3612 = (

let uu____3619 = (FStar_Util.pimap_empty ())
in (FStar_Util.dflt uu____3619 pimap_opt))
in (FStar_Util.pimap_add uu____3612 (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)))))


let add_fvar_binding : fvar_binding  ->  (fvar_binding FStar_Util.psmap * fvar_binding Prims.list)  ->  (fvar_binding FStar_Util.psmap * fvar_binding Prims.list) = (fun fvb uu____3666 -> (match (uu____3666) with
| (fvb_map, fvb_list) -> begin
(

let uu____3693 = (FStar_Util.psmap_add fvb_map fvb.fvar_lid.FStar_Ident.str fvb)
in ((uu____3693), ((fvb)::fvb_list)))
end))


let fresh_fvar : Prims.string  ->  Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun mname x s -> (

let xsym = (varops.fresh mname x)
in (

let uu____3727 = (

let uu____3728 = (FStar_SMTEncoding_Term.mk_fv ((xsym), (s)))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3728))
in ((xsym), (uu____3727)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (Prims.op_Hat "@x" (Prims.string_of_int env.depth))
in (

let y = (

let uu____3753 = (FStar_SMTEncoding_Term.mk_fv ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3753))
in (

let uu____3755 = (

let uu___241_3756 = env
in (

let uu____3757 = (add_bvar_binding ((x), (y)) env.bvar_bindings)
in {bvar_bindings = uu____3757; fvar_bindings = uu___241_3756.fvar_bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___241_3756.tcenv; warn = uu___241_3756.warn; nolabels = uu___241_3756.nolabels; use_zfuel_name = uu___241_3756.use_zfuel_name; encode_non_total_function_typ = uu___241_3756.encode_non_total_function_typ; current_module_name = uu___241_3756.current_module_name; encoding_quantifier = uu___241_3756.encoding_quantifier; global_cache = uu___241_3756.global_cache}))
in ((ysym), (y), (uu____3755))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in (

let uu____3792 = (

let uu___247_3793 = env
in (

let uu____3794 = (add_bvar_binding ((x), (y)) env.bvar_bindings)
in {bvar_bindings = uu____3794; fvar_bindings = uu___247_3793.fvar_bindings; depth = uu___247_3793.depth; tcenv = uu___247_3793.tcenv; warn = uu___247_3793.warn; nolabels = uu___247_3793.nolabels; use_zfuel_name = uu___247_3793.use_zfuel_name; encode_non_total_function_typ = uu___247_3793.encode_non_total_function_typ; current_module_name = uu___247_3793.current_module_name; encoding_quantifier = uu___247_3793.encoding_quantifier; global_cache = uu___247_3793.global_cache}))
in ((ysym), (y), (uu____3792))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in (

let uu____3835 = (

let uu___254_3836 = env
in (

let uu____3837 = (add_bvar_binding ((x), (y)) env.bvar_bindings)
in {bvar_bindings = uu____3837; fvar_bindings = uu___254_3836.fvar_bindings; depth = uu___254_3836.depth; tcenv = uu___254_3836.tcenv; warn = uu___254_3836.warn; nolabels = uu___254_3836.nolabels; use_zfuel_name = uu___254_3836.use_zfuel_name; encode_non_total_function_typ = uu___254_3836.encode_non_total_function_typ; current_module_name = uu___254_3836.current_module_name; encoding_quantifier = uu___254_3836.encoding_quantifier; global_cache = uu___254_3836.global_cache}))
in ((ysym), (y), (uu____3835))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___259_3863 = env
in (

let uu____3864 = (add_bvar_binding ((x), (t)) env.bvar_bindings)
in {bvar_bindings = uu____3864; fvar_bindings = uu___259_3863.fvar_bindings; depth = uu___259_3863.depth; tcenv = uu___259_3863.tcenv; warn = uu___259_3863.warn; nolabels = uu___259_3863.nolabels; use_zfuel_name = uu___259_3863.use_zfuel_name; encode_non_total_function_typ = uu___259_3863.encode_non_total_function_typ; current_module_name = uu___259_3863.current_module_name; encoding_quantifier = uu___259_3863.encoding_quantifier; global_cache = uu___259_3863.global_cache})))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____3884 = (lookup_bvar_binding env a)
in (match (uu____3884) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3895 = (lookup_bvar_binding env a)
in (match (uu____3895) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3906 = (

let uu____3908 = (FStar_Syntax_Print.bv_to_string a)
in (

let uu____3910 = (print_env env)
in (FStar_Util.format2 "Bound term variable not found  %s in environment: %s" uu____3908 uu____3910)))
in (failwith uu____3906))
end
| FStar_Pervasives_Native.Some (b, t) -> begin
t
end))
end
| FStar_Pervasives_Native.Some (b, t) -> begin
t
end)))


let mk_fvb : FStar_Ident.lident  ->  Prims.string  ->  Prims.int  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  Prims.bool  ->  fvar_binding = (fun lid fname arity ftok fuel_partial_app thunked -> (

let fvb = {fvar_lid = lid; smt_arity = arity; smt_id = fname; smt_token = ftok; smt_fuel_partial_app = fuel_partial_app; fvb_thunked = thunked}
in ((check_valid_fvb fvb);
fvb;
)))


let new_term_constant_and_tok_from_lid_aux : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.bool  ->  (Prims.string * Prims.string FStar_Pervasives_Native.option * env_t) = (fun env x arity thunked -> (

let fname = (varops.new_fvar x)
in (

let uu____4009 = (match (thunked) with
| true -> begin
((FStar_Pervasives_Native.None), (FStar_Pervasives_Native.None))
end
| uu____4035 -> begin
(

let ftok_name = (Prims.op_Hat fname "@tok")
in (

let ftok = (FStar_SMTEncoding_Util.mkApp ((ftok_name), ([])))
in ((FStar_Pervasives_Native.Some (ftok_name)), (FStar_Pervasives_Native.Some (ftok)))))
end)
in (match (uu____4009) with
| (ftok_name, ftok) -> begin
(

let fvb = (mk_fvb x fname arity ftok FStar_Pervasives_Native.None thunked)
in (

let uu____4073 = (

let uu___293_4074 = env
in (

let uu____4075 = (add_fvar_binding fvb env.fvar_bindings)
in {bvar_bindings = uu___293_4074.bvar_bindings; fvar_bindings = uu____4075; depth = uu___293_4074.depth; tcenv = uu___293_4074.tcenv; warn = uu___293_4074.warn; nolabels = uu___293_4074.nolabels; use_zfuel_name = uu___293_4074.use_zfuel_name; encode_non_total_function_typ = uu___293_4074.encode_non_total_function_typ; current_module_name = uu___293_4074.current_module_name; encoding_quantifier = uu___293_4074.encoding_quantifier; global_cache = uu___293_4074.global_cache}))
in ((fname), (ftok_name), (uu____4073))))
end))))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  (Prims.string * Prims.string * env_t) = (fun env x arity -> (

let uu____4114 = (new_term_constant_and_tok_from_lid_aux env x arity false)
in (match (uu____4114) with
| (fname, ftok_name_opt, env1) -> begin
(

let uu____4145 = (FStar_Option.get ftok_name_opt)
in ((fname), (uu____4145), (env1)))
end)))


let new_term_constant_and_tok_from_lid_maybe_thunked : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.bool  ->  (Prims.string * Prims.string FStar_Pervasives_Native.option * env_t) = (fun env x arity th -> (new_term_constant_and_tok_from_lid_aux env x arity th))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  fvar_binding = (fun env a -> (

let uu____4196 = (lookup_fvar_binding env a)
in (match (uu____4196) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4199 = (

let uu____4201 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____4201))
in (failwith uu____4199))
end
| FStar_Pervasives_Native.Some (s) -> begin
((check_valid_fvb s);
s;
)
end)))


let push_free_var_maybe_thunked : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  Prims.bool  ->  env_t = (fun env x arity fname ftok thunked -> (

let fvb = (mk_fvb x fname arity ftok FStar_Pervasives_Native.None thunked)
in (

let uu___319_4248 = env
in (

let uu____4249 = (add_fvar_binding fvb env.fvar_bindings)
in {bvar_bindings = uu___319_4248.bvar_bindings; fvar_bindings = uu____4249; depth = uu___319_4248.depth; tcenv = uu___319_4248.tcenv; warn = uu___319_4248.warn; nolabels = uu___319_4248.nolabels; use_zfuel_name = uu___319_4248.use_zfuel_name; encode_non_total_function_typ = uu___319_4248.encode_non_total_function_typ; current_module_name = uu___319_4248.current_module_name; encoding_quantifier = uu___319_4248.encoding_quantifier; global_cache = uu___319_4248.global_cache}))))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  env_t = (fun env x arity fname ftok -> (push_free_var_maybe_thunked env x arity fname ftok false))


let push_free_var_thunk : env_t  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  env_t = (fun env x arity fname ftok -> (push_free_var_maybe_thunked env x arity fname ftok (Prims.op_Equality arity (Prims.parse_int "0"))))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let fvb = (lookup_lid env x)
in (

let t3 = (

let uu____4349 = (

let uu____4357 = (

let uu____4360 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____4360)::[])
in ((f), (uu____4357)))
in (FStar_SMTEncoding_Util.mkApp uu____4349))
in (

let fvb1 = (mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token (FStar_Pervasives_Native.Some (t3)) false)
in (

let uu___337_4370 = env
in (

let uu____4371 = (add_fvar_binding fvb1 env.fvar_bindings)
in {bvar_bindings = uu___337_4370.bvar_bindings; fvar_bindings = uu____4371; depth = uu___337_4370.depth; tcenv = uu___337_4370.tcenv; warn = uu___337_4370.warn; nolabels = uu___337_4370.nolabels; use_zfuel_name = uu___337_4370.use_zfuel_name; encode_non_total_function_typ = uu___337_4370.encode_non_total_function_typ; current_module_name = uu___337_4370.current_module_name; encoding_quantifier = uu___337_4370.encoding_quantifier; global_cache = uu___337_4370.global_cache}))))))


let force_thunk : fvar_binding  ->  FStar_SMTEncoding_Term.term = (fun fvb -> ((match (((not (fvb.fvb_thunked)) || (Prims.op_disEquality fvb.smt_arity (Prims.parse_int "0")))) with
| true -> begin
(failwith "Forcing a non-thunk in the SMT encoding")
end
| uu____4391 -> begin
()
end);
(FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV ((fvb.smt_id), (FStar_SMTEncoding_Term.Term_sort), (true)));
))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____4409 = (lookup_fvar_binding env l)
in (match (uu____4409) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (fvb) -> begin
((

let uu____4416 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("PartialApp")))
in (match (uu____4416) with
| true -> begin
(

let uu____4421 = (FStar_Ident.string_of_lid l)
in (

let uu____4423 = (fvb_to_string fvb)
in (FStar_Util.print2 "Looked up %s found\n%s\n" uu____4421 uu____4423)))
end
| uu____4426 -> begin
()
end));
(match (fvb.fvb_thunked) with
| true -> begin
(

let uu____4431 = (force_thunk fvb)
in FStar_Pervasives_Native.Some (uu____4431))
end
| uu____4432 -> begin
(match (fvb.smt_fuel_partial_app) with
| FStar_Pervasives_Native.Some (f) when env.use_zfuel_name -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____4437 -> begin
(match (fvb.smt_token) with
| FStar_Pervasives_Native.Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____4445, (fuel)::[]) -> begin
(

let uu____4449 = (

let uu____4451 = (

let uu____4453 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____4453 FStar_SMTEncoding_Term.fv_name))
in (FStar_Util.starts_with uu____4451 "fuel"))
in (match (uu____4449) with
| true -> begin
(

let uu____4459 = (

let uu____4460 = (

let uu____4461 = (FStar_SMTEncoding_Term.mk_fv ((fvb.smt_id), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____4461))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____4460 fuel))
in (FStar_All.pipe_left (fun _4465 -> FStar_Pervasives_Native.Some (_4465)) uu____4459))
end
| uu____4466 -> begin
FStar_Pervasives_Native.Some (t)
end))
end
| uu____4468 -> begin
FStar_Pervasives_Native.Some (t)
end)
end
| uu____4469 -> begin
FStar_Pervasives_Native.None
end)
end)
end);
)
end)))


let lookup_free_var : env_t  ->  FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____4487 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____4487) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4491 = (

let uu____4493 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____4493))
in (failwith uu____4491))
end)))


let lookup_free_var_name : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  fvar_binding = (fun env a -> (lookup_lid env a.FStar_Syntax_Syntax.v))


let lookup_free_var_sym : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  ((FStar_SMTEncoding_Term.op, FStar_SMTEncoding_Term.term) FStar_Util.either * FStar_SMTEncoding_Term.term Prims.list * Prims.int) = (fun env a -> (

let fvb = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (fvb.smt_fuel_partial_app) with
| FStar_Pervasives_Native.Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____4555; FStar_SMTEncoding_Term.rng = uu____4556}) when env.use_zfuel_name -> begin
((FStar_Util.Inl (g)), (zf), ((fvb.smt_arity + (Prims.parse_int "1"))))
end
| uu____4581 -> begin
(match (fvb.smt_token) with
| FStar_Pervasives_Native.None when fvb.fvb_thunked -> begin
(

let uu____4597 = (

let uu____4602 = (force_thunk fvb)
in FStar_Util.Inr (uu____4602))
in ((uu____4597), ([]), (fvb.smt_arity)))
end
| FStar_Pervasives_Native.None -> begin
((FStar_Util.Inl (FStar_SMTEncoding_Term.Var (fvb.smt_id))), ([]), (fvb.smt_arity))
end
| FStar_Pervasives_Native.Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((FStar_Util.Inl (g)), ((fuel)::[]), ((fvb.smt_arity + (Prims.parse_int "1"))))
end
| uu____4643 -> begin
((FStar_Util.Inl (FStar_SMTEncoding_Term.Var (fvb.smt_id))), ([]), (fvb.smt_arity))
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env nm -> (

let uu____4666 = (

let uu____4669 = (FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst)
in (FStar_Util.psmap_find_map uu____4669 (fun uu____4689 fvb -> ((check_valid_fvb fvb);
(match ((Prims.op_Equality fvb.smt_id nm)) with
| true -> begin
fvb.smt_token
end
| uu____4697 -> begin
FStar_Pervasives_Native.None
end);
))))
in (match (uu____4666) with
| FStar_Pervasives_Native.Some (b) -> begin
FStar_Pervasives_Native.Some (b)
end
| FStar_Pervasives_Native.None -> begin
(FStar_Util.psmap_find_map env.bvar_bindings (fun uu____4710 pi -> (FStar_Util.pimap_fold pi (fun uu____4730 y res -> (match (((res), (y))) with
| (FStar_Pervasives_Native.Some (uu____4748), uu____4749) -> begin
res
end
| (FStar_Pervasives_Native.None, (uu____4760, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (sym), []); FStar_SMTEncoding_Term.freevars = uu____4762; FStar_SMTEncoding_Term.rng = uu____4763})) when (Prims.op_Equality sym nm) -> begin
FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.snd y))
end
| uu____4786 -> begin
FStar_Pervasives_Native.None
end)) FStar_Pervasives_Native.None)))
end)))


let reset_current_module_fvbs : env_t  ->  env_t = (fun env -> (

let uu___424_4803 = env
in (

let uu____4804 = (

let uu____4813 = (FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst)
in ((uu____4813), ([])))
in {bvar_bindings = uu___424_4803.bvar_bindings; fvar_bindings = uu____4804; depth = uu___424_4803.depth; tcenv = uu___424_4803.tcenv; warn = uu___424_4803.warn; nolabels = uu___424_4803.nolabels; use_zfuel_name = uu___424_4803.use_zfuel_name; encode_non_total_function_typ = uu___424_4803.encode_non_total_function_typ; current_module_name = uu___424_4803.current_module_name; encoding_quantifier = uu___424_4803.encoding_quantifier; global_cache = uu___424_4803.global_cache})))


let get_current_module_fvbs : env_t  ->  fvar_binding Prims.list = (fun env -> (FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.snd))


let add_fvar_binding_to_env : fvar_binding  ->  env_t  ->  env_t = (fun fvb env -> (

let uu___429_4867 = env
in (

let uu____4868 = (add_fvar_binding fvb env.fvar_bindings)
in {bvar_bindings = uu___429_4867.bvar_bindings; fvar_bindings = uu____4868; depth = uu___429_4867.depth; tcenv = uu___429_4867.tcenv; warn = uu___429_4867.warn; nolabels = uu___429_4867.nolabels; use_zfuel_name = uu___429_4867.use_zfuel_name; encode_non_total_function_typ = uu___429_4867.encode_non_total_function_typ; current_module_name = uu___429_4867.current_module_name; encoding_quantifier = uu___429_4867.encoding_quantifier; global_cache = uu___429_4867.global_cache})))





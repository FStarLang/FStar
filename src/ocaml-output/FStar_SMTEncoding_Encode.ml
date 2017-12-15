
open Prims
open FStar_Pervasives

let add_fuel : 'Auu____7 . 'Auu____7  ->  'Auu____7 Prims.list  ->  'Auu____7 Prims.list = (fun x tl1 -> (

let uu____22 = (FStar_Options.unthrottle_inductives ())
in (match (uu____22) with
| true -> begin
tl1
end
| uu____25 -> begin
(x)::tl1
end)))


let withenv : 'Auu____36 'Auu____37 'Auu____38 . 'Auu____38  ->  ('Auu____37 * 'Auu____36)  ->  ('Auu____37 * 'Auu____36 * 'Auu____38) = (fun c uu____56 -> (match (uu____56) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs : 'Auu____71 'Auu____72 'Auu____73 . (('Auu____73, 'Auu____72) FStar_Util.either * 'Auu____71) Prims.list  ->  (('Auu____73, 'Auu____72) FStar_Util.either * 'Auu____71) Prims.list = (fun args -> (FStar_List.filter (fun uu___125_119 -> (match (uu___125_119) with
| (FStar_Util.Inl (uu____128), uu____129) -> begin
false
end
| uu____134 -> begin
true
end)) args))


let subst_lcomp_opt : 'Auu____149 . FStar_Syntax_Syntax.subst_elt Prims.list  ->  (FStar_Syntax_Syntax.lcomp, 'Auu____149) FStar_Util.either FStar_Pervasives_Native.option  ->  (FStar_Syntax_Syntax.lcomp, 'Auu____149) FStar_Util.either FStar_Pervasives_Native.option = (fun s l -> (match (l) with
| FStar_Pervasives_Native.Some (FStar_Util.Inl (l1)) -> begin
(

let uu____185 = (

let uu____190 = (

let uu____191 = (

let uu____194 = (l1.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s uu____194))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____191))
in FStar_Util.Inl (uu____190))
in FStar_Pervasives_Native.Some (uu____185))
end
| uu____201 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s 39 (*'*) 95 (*_*)))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a1 = (

let uu___148_221 = a
in (

let uu____222 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____222; FStar_Syntax_Syntax.index = uu___148_221.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___148_221.FStar_Syntax_Syntax.sort}))
in (

let uu____223 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a1.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape uu____223))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun uu____239 -> (

let uu____240 = (FStar_Util.format2 "Projector %s on data constructor %s not found" (Prims.string_of_int i) lid.FStar_Ident.str)
in (failwith uu____240)))
in (

let uu____241 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (uu____241) with
| (uu____246, t) -> begin
(

let uu____248 = (

let uu____249 = (FStar_Syntax_Subst.compress t)
in uu____249.FStar_Syntax_Syntax.n)
in (match (uu____248) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____270 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____270) with
| (binders, uu____276) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____281 -> begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (FStar_Pervasives_Native.fst b)))
end)
end))
end
| uu____291 -> begin
(fail ())
end))
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (

let uu____300 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str (Prims.string_of_int i))
in (FStar_All.pipe_left escape uu____300)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (

let uu____309 = (

let uu____314 = (mk_term_projector_name lid a)
in ((uu____314), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____309)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (

let uu____323 = (

let uu____328 = (mk_term_projector_name_by_pos lid i)
in ((uu____328), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____323)))


let mk_data_tester : 'Auu____337 . 'Auu____337  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let __proj__Mkvarops_t__item__push : varops_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__push
end))


let __proj__Mkvarops_t__item__pop : varops_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__pop
end))


let __proj__Mkvarops_t__item__new_var : varops_t  ->  FStar_Ident.ident  ->  Prims.int  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__new_var
end))


let __proj__Mkvarops_t__item__new_fvar : varops_t  ->  FStar_Ident.lident  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__new_fvar
end))


let __proj__Mkvarops_t__item__fresh : varops_t  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__fresh
end))


let __proj__Mkvarops_t__item__string_const : varops_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__string_const
end))


let __proj__Mkvarops_t__item__next_id : varops_t  ->  Prims.unit  ->  Prims.int = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__next_id
end))


let __proj__Mkvarops_t__item__mk_unique : varops_t  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__mk_unique
end))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun uu____718 -> (

let uu____719 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____722 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((uu____719), (uu____722)))))
in (

let scopes = (

let uu____742 = (

let uu____753 = (new_scope ())
in (uu____753)::[])
in (FStar_Util.mk_ref uu____742))
in (

let mk_unique = (fun y -> (

let y1 = (escape y)
in (

let y2 = (

let uu____794 = (

let uu____797 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____797 (fun uu____883 -> (match (uu____883) with
| (names1, uu____895) -> begin
(FStar_Util.smap_try_find names1 y1)
end))))
in (match (uu____794) with
| FStar_Pervasives_Native.None -> begin
y1
end
| FStar_Pervasives_Native.Some (uu____904) -> begin
((FStar_Util.incr ctr);
(

let uu____927 = (

let uu____928 = (

let uu____929 = (FStar_ST.op_Bang ctr)
in (Prims.string_of_int uu____929))
in (Prims.strcat "__" uu____928))
in (Prims.strcat y1 uu____927));
)
end))
in (

let top_scope = (

let uu____957 = (

let uu____966 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____966))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____957))
in ((FStar_Util.smap_add top_scope y2 true);
y2;
)))))
in (

let new_var = (fun pp rn -> (FStar_All.pipe_left mk_unique (Prims.strcat pp.FStar_Ident.idText (Prims.strcat "__" (Prims.string_of_int rn)))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id1 = (fun uu____1078 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
))
in (

let fresh1 = (fun pfx -> (

let uu____1129 = (

let uu____1130 = (next_id1 ())
in (FStar_All.pipe_left Prims.string_of_int uu____1130))
in (FStar_Util.format2 "%s_%s" pfx uu____1129)))
in (

let string_const = (fun s -> (

let uu____1135 = (

let uu____1138 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____1138 (fun uu____1224 -> (match (uu____1224) with
| (uu____1235, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____1135) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let id = (next_id1 ())
in (

let f = (

let uu____1248 = (FStar_SMTEncoding_Util.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1248))
in (

let top_scope = (

let uu____1252 = (

let uu____1261 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1261))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1252))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push1 = (fun uu____1362 -> (

let uu____1363 = (

let uu____1374 = (new_scope ())
in (

let uu____1383 = (FStar_ST.op_Bang scopes)
in (uu____1374)::uu____1383))
in (FStar_ST.op_Colon_Equals scopes uu____1363)))
in (

let pop1 = (fun uu____1533 -> (

let uu____1534 = (

let uu____1545 = (FStar_ST.op_Bang scopes)
in (FStar_List.tl uu____1545))
in (FStar_ST.op_Colon_Equals scopes uu____1534)))
in {push = push1; pop = pop1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique}))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let uu___149_1696 = x
in (

let uu____1697 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____1697; FStar_Syntax_Syntax.index = uu___149_1696.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___149_1696.FStar_Syntax_Syntax.sort})))

type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____1731 -> begin
false
end))


let __proj__Binding_var__item___0 : binding  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
_0
end))


let uu___is_Binding_fvar : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_fvar (_0) -> begin
true
end
| uu____1769 -> begin
false
end))


let __proj__Binding_fvar__item___0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_0) -> begin
_0
end))


let binder_of_eithervar : 'Auu____1820 'Auu____1821 . 'Auu____1821  ->  ('Auu____1821 * 'Auu____1820 FStar_Pervasives_Native.option) = (fun v1 -> ((v1), (FStar_Pervasives_Native.None)))

type cache_entry =
{cache_symbol_name : Prims.string; cache_symbol_arg_sorts : FStar_SMTEncoding_Term.sort Prims.list; cache_symbol_decls : FStar_SMTEncoding_Term.decl Prims.list; cache_symbol_assumption_names : Prims.string Prims.list}


let __proj__Mkcache_entry__item__cache_symbol_name : cache_entry  ->  Prims.string = (fun projectee -> (match (projectee) with
| {cache_symbol_name = __fname__cache_symbol_name; cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts; cache_symbol_decls = __fname__cache_symbol_decls; cache_symbol_assumption_names = __fname__cache_symbol_assumption_names} -> begin
__fname__cache_symbol_name
end))


let __proj__Mkcache_entry__item__cache_symbol_arg_sorts : cache_entry  ->  FStar_SMTEncoding_Term.sort Prims.list = (fun projectee -> (match (projectee) with
| {cache_symbol_name = __fname__cache_symbol_name; cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts; cache_symbol_decls = __fname__cache_symbol_decls; cache_symbol_assumption_names = __fname__cache_symbol_assumption_names} -> begin
__fname__cache_symbol_arg_sorts
end))


let __proj__Mkcache_entry__item__cache_symbol_decls : cache_entry  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun projectee -> (match (projectee) with
| {cache_symbol_name = __fname__cache_symbol_name; cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts; cache_symbol_decls = __fname__cache_symbol_decls; cache_symbol_assumption_names = __fname__cache_symbol_assumption_names} -> begin
__fname__cache_symbol_decls
end))


let __proj__Mkcache_entry__item__cache_symbol_assumption_names : cache_entry  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {cache_symbol_name = __fname__cache_symbol_name; cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts; cache_symbol_decls = __fname__cache_symbol_decls; cache_symbol_assumption_names = __fname__cache_symbol_assumption_names} -> begin
__fname__cache_symbol_assumption_names
end))

type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : cache_entry FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool; current_module_name : Prims.string}


let __proj__Mkenv_t__item__bindings : env_t  ->  binding Prims.list = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__bindings
end))


let __proj__Mkenv_t__item__depth : env_t  ->  Prims.int = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__depth
end))


let __proj__Mkenv_t__item__tcenv : env_t  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__tcenv
end))


let __proj__Mkenv_t__item__warn : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__warn
end))


let __proj__Mkenv_t__item__cache : env_t  ->  cache_entry FStar_Util.smap = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__cache
end))


let __proj__Mkenv_t__item__nolabels : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__nolabels
end))


let __proj__Mkenv_t__item__use_zfuel_name : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__use_zfuel_name
end))


let __proj__Mkenv_t__item__encode_non_total_function_typ : env_t  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__encode_non_total_function_typ
end))


let __proj__Mkenv_t__item__current_module_name : env_t  ->  Prims.string = (fun projectee -> (match (projectee) with
| {bindings = __fname__bindings; depth = __fname__depth; tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache; nolabels = __fname__nolabels; use_zfuel_name = __fname__use_zfuel_name; encode_non_total_function_typ = __fname__encode_non_total_function_typ; current_module_name = __fname__current_module_name} -> begin
__fname__current_module_name
end))


let mk_cache_entry : 'Auu____2135 . 'Auu____2135  ->  Prims.string  ->  FStar_SMTEncoding_Term.sort Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  cache_entry = (fun env tsym cvar_sorts t_decls -> (

let names1 = (FStar_All.pipe_right t_decls (FStar_List.collect (fun uu___126_2169 -> (match (uu___126_2169) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(a.FStar_SMTEncoding_Term.assumption_name)::[]
end
| uu____2173 -> begin
[]
end))))
in {cache_symbol_name = tsym; cache_symbol_arg_sorts = cvar_sorts; cache_symbol_decls = t_decls; cache_symbol_assumption_names = names1}))


let use_cache_entry : cache_entry  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun ce -> (FStar_SMTEncoding_Term.RetainAssumptions (ce.cache_symbol_assumption_names))::[])


let print_env : env_t  ->  Prims.string = (fun e -> (

let uu____2184 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun uu___127_2194 -> (match (uu___127_2194) with
| Binding_var (x, uu____2196) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, uu____2198, uu____2199, uu____2200) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right uu____2184 (FStar_String.concat ", "))))


let lookup_binding : 'Auu____2217 . env_t  ->  (binding  ->  'Auu____2217 FStar_Pervasives_Native.option)  ->  'Auu____2217 FStar_Pervasives_Native.option = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string FStar_Pervasives_Native.option = (fun env t -> (

let uu____2247 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____2247) with
| true -> begin
(

let uu____2250 = (FStar_Syntax_Print.term_to_string t)
in FStar_Pervasives_Native.Some (uu____2250))
end
| uu____2251 -> begin
FStar_Pervasives_Native.None
end)))


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (

let uu____2265 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (uu____2265)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (Prims.strcat "@x" (Prims.string_of_int env.depth))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let uu___150_2283 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___150_2283.tcenv; warn = uu___150_2283.warn; cache = uu___150_2283.cache; nolabels = uu___150_2283.nolabels; use_zfuel_name = uu___150_2283.use_zfuel_name; encode_non_total_function_typ = uu___150_2283.encode_non_total_function_typ; current_module_name = uu___150_2283.current_module_name}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___151_2303 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___151_2303.depth; tcenv = uu___151_2303.tcenv; warn = uu___151_2303.warn; cache = uu___151_2303.cache; nolabels = uu___151_2303.nolabels; use_zfuel_name = uu___151_2303.use_zfuel_name; encode_non_total_function_typ = uu___151_2303.encode_non_total_function_typ; current_module_name = uu___151_2303.current_module_name}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___152_2327 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___152_2327.depth; tcenv = uu___152_2327.tcenv; warn = uu___152_2327.warn; cache = uu___152_2327.cache; nolabels = uu___152_2327.nolabels; use_zfuel_name = uu___152_2327.use_zfuel_name; encode_non_total_function_typ = uu___152_2327.encode_non_total_function_typ; current_module_name = uu___152_2327.current_module_name}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___153_2340 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = uu___153_2340.depth; tcenv = uu___153_2340.tcenv; warn = uu___153_2340.warn; cache = uu___153_2340.cache; nolabels = uu___153_2340.nolabels; use_zfuel_name = uu___153_2340.use_zfuel_name; encode_non_total_function_typ = uu___153_2340.encode_non_total_function_typ; current_module_name = uu___153_2340.current_module_name}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun uu___128_2366 -> (match (uu___128_2366) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
FStar_Pervasives_Native.Some (((b), (t)))
end
| uu____2379 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____2384 = (aux a)
in (match (uu____2384) with
| FStar_Pervasives_Native.None -> begin
(

let a2 = (unmangle a)
in (

let uu____2396 = (aux a2)
in (match (uu____2396) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2407 = (

let uu____2408 = (FStar_Syntax_Print.bv_to_string a2)
in (

let uu____2409 = (print_env env)
in (FStar_Util.format2 "Bound term variable not found (after unmangling): %s in environment: %s" uu____2408 uu____2409)))
in (failwith uu____2407))
end
| FStar_Pervasives_Native.Some (b, t) -> begin
t
end)))
end
| FStar_Pervasives_Native.Some (b, t) -> begin
t
end))))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (

let uu____2438 = (

let uu___154_2439 = env
in (

let uu____2440 = (

let uu____2443 = (

let uu____2444 = (

let uu____2457 = (

let uu____2460 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)) uu____2460))
in ((x), (fname), (uu____2457), (FStar_Pervasives_Native.None)))
in Binding_fvar (uu____2444))
in (uu____2443)::env.bindings)
in {bindings = uu____2440; depth = uu___154_2439.depth; tcenv = uu___154_2439.tcenv; warn = uu___154_2439.warn; cache = uu___154_2439.cache; nolabels = uu___154_2439.nolabels; use_zfuel_name = uu___154_2439.use_zfuel_name; encode_non_total_function_typ = uu___154_2439.encode_non_total_function_typ; current_module_name = uu___154_2439.current_module_name}))
in ((fname), (ftok), (uu____2438))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) FStar_Pervasives_Native.option = (fun env a -> (lookup_binding env (fun uu___129_2504 -> (match (uu___129_2504) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
FStar_Pervasives_Native.Some (((t1), (t2), (t3)))
end
| uu____2543 -> begin
FStar_Pervasives_Native.None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (

let uu____2562 = (lookup_binding env (fun uu___130_2570 -> (match (uu___130_2570) with
| Binding_fvar (b, t1, t2, t3) when (Prims.op_Equality b.FStar_Ident.str s) -> begin
FStar_Pervasives_Native.Some (())
end
| uu____2585 -> begin
FStar_Pervasives_Native.None
end)))
in (FStar_All.pipe_right uu____2562 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) = (fun env a -> (

let uu____2606 = (try_lookup_lid env a)
in (match (uu____2606) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2639 = (

let uu____2640 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____2640))
in (failwith uu____2639))
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  env_t = (fun env x fname ftok -> (

let uu___155_2692 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (FStar_Pervasives_Native.None))))::env.bindings; depth = uu___155_2692.depth; tcenv = uu___155_2692.tcenv; warn = uu___155_2692.warn; cache = uu___155_2692.cache; nolabels = uu___155_2692.nolabels; use_zfuel_name = uu___155_2692.use_zfuel_name; encode_non_total_function_typ = uu___155_2692.encode_non_total_function_typ; current_module_name = uu___155_2692.current_module_name}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let uu____2709 = (lookup_lid env x)
in (match (uu____2709) with
| (t1, t2, uu____2722) -> begin
(

let t3 = (

let uu____2732 = (

let uu____2739 = (

let uu____2742 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____2742)::[])
in ((f), (uu____2739)))
in (FStar_SMTEncoding_Util.mkApp uu____2732))
in (

let uu___156_2747 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (FStar_Pervasives_Native.Some (t3)))))::env.bindings; depth = uu___156_2747.depth; tcenv = uu___156_2747.tcenv; warn = uu___156_2747.warn; cache = uu___156_2747.cache; nolabels = uu___156_2747.nolabels; use_zfuel_name = uu___156_2747.use_zfuel_name; encode_non_total_function_typ = uu___156_2747.encode_non_total_function_typ; current_module_name = uu___156_2747.current_module_name}))
end)))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____2762 = (try_lookup_lid env l)
in (match (uu____2762) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| FStar_Pervasives_Native.Some (f) when env.use_zfuel_name -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____2811 -> begin
(match (sym) with
| FStar_Pervasives_Native.Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____2819, (fuel)::[]) -> begin
(

let uu____2823 = (

let uu____2824 = (

let uu____2825 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____2825 FStar_Pervasives_Native.fst))
in (FStar_Util.starts_with uu____2824 "fuel"))
in (match (uu____2823) with
| true -> begin
(

let uu____2828 = (

let uu____2829 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____2829 fuel))
in (FStar_All.pipe_left (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42)) uu____2828))
end
| uu____2832 -> begin
FStar_Pervasives_Native.Some (t)
end))
end
| uu____2833 -> begin
FStar_Pervasives_Native.Some (t)
end)
end
| uu____2834 -> begin
FStar_Pervasives_Native.None
end)
end)
end)))


let lookup_free_var : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____2849 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____2849) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2853 = (

let uu____2854 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____2854))
in (failwith uu____2853))
end)))


let lookup_free_var_name : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  Prims.string = (fun env a -> (

let uu____2867 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____2867) with
| (x, uu____2879, uu____2880) -> begin
x
end)))


let lookup_free_var_sym : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  (FStar_SMTEncoding_Term.op * FStar_SMTEncoding_Term.term Prims.list) = (fun env a -> (

let uu____2907 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____2907) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| FStar_Pervasives_Native.Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____2943; FStar_SMTEncoding_Term.rng = uu____2944}) when env.use_zfuel_name -> begin
((g), (zf))
end
| uu____2959 -> begin
(match (sym) with
| FStar_Pervasives_Native.None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| FStar_Pervasives_Native.Some (sym1) -> begin
(match (sym1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| uu____2983 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___131_3001 -> (match (uu___131_3001) with
| Binding_fvar (uu____3004, nm', tok, uu____3007) when (Prims.op_Equality nm nm') -> begin
tok
end
| uu____3016 -> begin
FStar_Pervasives_Native.None
end))))


let mkForall_fuel' : 'Auu____3023 . 'Auu____3023  ->  (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (fun n1 uu____3041 -> (match (uu____3041) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____3066 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____3071 = (FStar_Options.unthrottle_inductives ())
in (match (uu____3071) with
| true -> begin
(fallback ())
end
| uu____3072 -> begin
(

let uu____3073 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____3073) with
| (fsym, fterm) -> begin
(

let add_fuel1 = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____3104 -> begin
p
end)))))
in (

let pats1 = (FStar_List.map add_fuel1 pats)
in (

let body1 = (match (body.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (guard)::(body')::[]) -> begin
(

let guard1 = (match (guard.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, guards) -> begin
(

let uu____3125 = (add_fuel1 guards)
in (FStar_SMTEncoding_Util.mk_and_l uu____3125))
end
| uu____3128 -> begin
(

let uu____3129 = (add_fuel1 ((guard)::[]))
in (FStar_All.pipe_right uu____3129 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard1), (body'))))
end
| uu____3134 -> begin
body
end)
in (

let vars1 = (((fsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars
in (FStar_SMTEncoding_Util.mkForall ((pats1), (vars1), (body1)))))))
end))
end)))
end))


let mkForall_fuel : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' (Prims.parse_int "1"))


let head_normal : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3178) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____3191) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3198) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3199) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____3216) -> begin
true
end
| FStar_Syntax_Syntax.Tm_constant (uu____3233) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3235 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3235 FStar_Option.isNone))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____3253; FStar_Syntax_Syntax.vars = uu____3254}, uu____3255) -> begin
(

let uu____3276 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3276 FStar_Option.isNone))
end
| uu____3293 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____3302 = (

let uu____3303 = (FStar_Syntax_Util.un_uinst t)
in uu____3303.FStar_Syntax_Syntax.n)
in (match (uu____3302) with
| FStar_Syntax_Syntax.Tm_abs (uu____3306, uu____3307, FStar_Pervasives_Native.Some (rc)) -> begin
(((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___132_3328 -> (match (uu___132_3328) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____3329 -> begin
false
end)) rc.FStar_Syntax_Syntax.residual_flags))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3331 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3331 FStar_Option.isSome))
end
| uu____3348 -> begin
false
end)))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____3357 = (head_normal env t)
in (match (uu____3357) with
| true -> begin
t
end
| uu____3358 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____3371 = (

let uu____3372 = (FStar_Syntax_Syntax.null_binder t)
in (uu____3372)::[])
in (

let uu____3373 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.abs uu____3371 uu____3373 FStar_Pervasives_Native.None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((FStar_Pervasives_Native.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(

let uu____3413 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out uu____3413))
end
| s -> begin
(

let uu____3418 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out uu____3418))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___133_3436 -> (match (uu___133_3436) with
| FStar_SMTEncoding_Term.Var ("ApplyTT") -> begin
true
end
| FStar_SMTEncoding_Term.Var ("ApplyTF") -> begin
true
end
| uu____3437 -> begin
false
end))


let is_an_eta_expansion : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env vars body -> (

let rec check_partial_applications = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____3476; FStar_SMTEncoding_Term.rng = uu____3477})::[]), (x)::xs1) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(check_partial_applications f xs1)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____3500) -> begin
(

let uu____3509 = ((Prims.op_Equality (FStar_List.length args) (FStar_List.length xs)) && (FStar_List.forall2 (fun a v1 -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v1)
end
| uu____3520 -> begin
false
end)) args (FStar_List.rev xs)))
in (match (uu____3509) with
| true -> begin
(tok_of_name env f)
end
| uu____3523 -> begin
FStar_Pervasives_Native.None
end))
end
| (uu____3524, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____3528 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (

let uu____3532 = (FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)
in (not (uu____3532))))))
in (match (uu____3528) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____3535 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____3536 -> begin
FStar_Pervasives_Native.None
end))
in (check_partial_applications body (FStar_List.rev vars))))


type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)


type labels =
label Prims.list

type pattern =
{pat_vars : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t); guard : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term; projections : FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list}


let __proj__Mkpattern__item__pat_vars : pattern  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list = (fun projectee -> (match (projectee) with
| {pat_vars = __fname__pat_vars; pat_term = __fname__pat_term; guard = __fname__guard; projections = __fname__projections} -> begin
__fname__pat_vars
end))


let __proj__Mkpattern__item__pat_term : pattern  ->  Prims.unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun projectee -> (match (projectee) with
| {pat_vars = __fname__pat_vars; pat_term = __fname__pat_term; guard = __fname__guard; projections = __fname__projections} -> begin
__fname__pat_term
end))


let __proj__Mkpattern__item__guard : pattern  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun projectee -> (match (projectee) with
| {pat_vars = __fname__pat_vars; pat_term = __fname__pat_term; guard = __fname__guard; projections = __fname__projections} -> begin
__fname__guard
end))


let __proj__Mkpattern__item__projections : pattern  ->  FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list = (fun projectee -> (match (projectee) with
| {pat_vars = __fname__pat_vars; pat_term = __fname__pat_term; guard = __fname__guard; projections = __fname__projections} -> begin
__fname__projections
end))

exception Let_rec_unencodeable


let uu___is_Let_rec_unencodeable : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Let_rec_unencodeable -> begin
true
end
| uu____3766 -> begin
false
end))

exception Inner_let_rec


let uu___is_Inner_let_rec : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inner_let_rec -> begin
true
end
| uu____3771 -> begin
false
end))


let as_function_typ : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3792) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_refine (uu____3805) -> begin
(

let uu____3812 = (FStar_Syntax_Util.unrefine t1)
in (aux true uu____3812))
end
| uu____3813 -> begin
(match (norm1) with
| true -> begin
(

let uu____3814 = (whnf env t1)
in (aux false uu____3814))
end
| uu____3815 -> begin
(

let uu____3816 = (

let uu____3817 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____3818 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____3817 uu____3818)))
in (failwith uu____3816))
end)
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| uu____3850 -> begin
(

let uu____3851 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____3851)))
end)))


let is_arithmetic_primitive : 'Auu____3868 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____3868 Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____3888)::(uu____3889)::[]) -> begin
(((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Subtraction)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____3893)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus)
end
| uu____3896 -> begin
false
end))


let isInteger : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
true
end
| uu____3918 -> begin
false
end))


let getInteger : FStar_Syntax_Syntax.term'  ->  Prims.int = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
(FStar_Util.int_of_string n1)
end
| uu____3934 -> begin
(failwith "Expected an Integer term")
end))


let is_BitVector_primitive : 'Auu____3941 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____3941) Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____3980))::(uu____3981)::(uu____3982)::[]) -> begin
((((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_and_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_xor_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_left_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_right_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_udiv_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mod_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____4033))::(uu____4034)::[]) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_to_nat_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| uu____4071 -> begin
false
end))


let rec encode_const : FStar_Const.sconst  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun c env -> (match (c) with
| FStar_Const.Const_unit -> begin
((FStar_SMTEncoding_Term.mk_Term_unit), ([]))
end
| FStar_Const.Const_bool (true) -> begin
(

let uu____4278 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((uu____4278), ([])))
end
| FStar_Const.Const_bool (false) -> begin
(

let uu____4281 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse)
in ((uu____4281), ([])))
end
| FStar_Const.Const_int (i, FStar_Pervasives_Native.None) -> begin
(

let uu____4295 = (

let uu____4296 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____4296))
in ((uu____4295), ([])))
end
| FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some (sw)) -> begin
(

let syntax_term = (FStar_ToSyntax_ToSyntax.desugar_machine_integer env.tcenv.FStar_TypeChecker_Env.dsenv repr sw FStar_Range.dummyRange)
in (encode_term syntax_term env))
end
| FStar_Const.Const_char (c1) -> begin
(

let repr = (FStar_Util.string_of_int (FStar_Util.int_of_char c1))
in (

let sw = ((FStar_Const.Unsigned), (FStar_Const.Int8))
in (

let syntax_term = (FStar_ToSyntax_ToSyntax.desugar_machine_integer env.tcenv.FStar_TypeChecker_Env.dsenv repr sw FStar_Range.dummyRange)
in (encode_term syntax_term env))))
end
| FStar_Const.Const_string (s, uu____4325) -> begin
(

let uu____4326 = (varops.string_const s)
in ((uu____4326), ([])))
end
| FStar_Const.Const_range (r) -> begin
((FStar_SMTEncoding_Term.mk_Range_const), ([]))
end
| FStar_Const.Const_effect -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| c1 -> begin
(

let uu____4335 = (

let uu____4336 = (FStar_Syntax_Print.const_to_string c1)
in (FStar_Util.format1 "Unhandled constant: %s" uu____4336))
in (failwith uu____4335))
end))
and encode_binders : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____4365 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4365) with
| true -> begin
(

let uu____4366 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____4366))
end
| uu____4367 -> begin
()
end));
(

let uu____4368 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____4452 b -> (match (uu____4452) with
| (vars, guards, env1, decls, names1) -> begin
(

let uu____4531 = (

let x = (unmangle (FStar_Pervasives_Native.fst b))
in (

let uu____4547 = (gen_term_var env1 x)
in (match (uu____4547) with
| (xxsym, xx, env') -> begin
(

let uu____4571 = (

let uu____4576 = (norm env1 x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____4576 env1 xx))
in (match (uu____4571) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____4531) with
| (v1, g, env2, decls', n1) -> begin
(((v1)::vars), ((g)::guards), (env2), ((FStar_List.append decls decls')), ((n1)::names1))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____4368) with
| (vars, guards, env1, decls, names1) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env1), (decls), ((FStar_List.rev names1)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____4735 = (encode_term t env)
in (match (uu____4735) with
| (t1, decls) -> begin
(

let uu____4746 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1)
in ((uu____4746), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____4757 = (encode_term t env)
in (match (uu____4757) with
| (t1, decls) -> begin
(match (fuel_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4772 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t1)
in ((uu____4772), (decls)))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____4774 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1)
in ((uu____4774), (decls)))
end)
end)))
and encode_arith_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.args  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun env head1 args_e -> (

let uu____4780 = (encode_args args_e env)
in (match (uu____4780) with
| (arg_tms, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____4799 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms1 -> (

let uu____4808 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____4808)))
in (

let binary = (fun arg_tms1 -> (

let uu____4821 = (

let uu____4822 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____4822))
in (

let uu____4823 = (

let uu____4824 = (

let uu____4825 = (FStar_List.tl arg_tms1)
in (FStar_List.hd uu____4825))
in (FStar_SMTEncoding_Term.unboxInt uu____4824))
in ((uu____4821), (uu____4823)))))
in (

let mk_default = (fun uu____4831 -> (

let uu____4832 = (lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____4832) with
| (fname, fuel_args) -> begin
(FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args arg_tms))))
end)))
in (

let mk_l = (fun op mk_args ts -> (

let uu____4883 = (FStar_Options.smtencoding_l_arith_native ())
in (match (uu____4883) with
| true -> begin
(

let uu____4884 = (

let uu____4885 = (mk_args ts)
in (op uu____4885))
in (FStar_All.pipe_right uu____4884 FStar_SMTEncoding_Term.boxInt))
end
| uu____4886 -> begin
(mk_default ())
end)))
in (

let mk_nl = (fun nm op ts -> (

let uu____4914 = (FStar_Options.smtencoding_nl_arith_wrapped ())
in (match (uu____4914) with
| true -> begin
(

let uu____4915 = (binary ts)
in (match (uu____4915) with
| (t1, t2) -> begin
(

let uu____4922 = (FStar_SMTEncoding_Util.mkApp ((nm), ((t1)::(t2)::[])))
in (FStar_All.pipe_right uu____4922 FStar_SMTEncoding_Term.boxInt))
end))
end
| uu____4925 -> begin
(

let uu____4926 = (FStar_Options.smtencoding_nl_arith_native ())
in (match (uu____4926) with
| true -> begin
(

let uu____4927 = (op (binary ts))
in (FStar_All.pipe_right uu____4927 FStar_SMTEncoding_Term.boxInt))
end
| uu____4928 -> begin
(mk_default ())
end))
end)))
in (

let add1 = (mk_l FStar_SMTEncoding_Util.mkAdd binary)
in (

let sub1 = (mk_l FStar_SMTEncoding_Util.mkSub binary)
in (

let minus = (mk_l FStar_SMTEncoding_Util.mkMinus unary)
in (

let mul1 = (mk_nl "_mul" FStar_SMTEncoding_Util.mkMul)
in (

let div1 = (mk_nl "_div" FStar_SMTEncoding_Util.mkDiv)
in (

let modulus = (mk_nl "_mod" FStar_SMTEncoding_Util.mkMod)
in (

let ops = (((FStar_Parser_Const.op_Addition), (add1)))::(((FStar_Parser_Const.op_Subtraction), (sub1)))::(((FStar_Parser_Const.op_Multiply), (mul1)))::(((FStar_Parser_Const.op_Division), (div1)))::(((FStar_Parser_Const.op_Modulus), (modulus)))::(((FStar_Parser_Const.op_Minus), (minus)))::[]
in (

let uu____5058 = (

let uu____5067 = (FStar_List.tryFind (fun uu____5089 -> (match (uu____5089) with
| (l, uu____5099) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____5067 FStar_Util.must))
in (match (uu____5058) with
| (uu____5138, op) -> begin
(

let uu____5148 = (op arg_tms)
in ((uu____5148), (decls)))
end)))))))))))))))
end)))
and encode_BitVector_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.arg Prims.list  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun env head1 args_e -> (

let uu____5156 = (FStar_List.hd args_e)
in (match (uu____5156) with
| (tm_sz, uu____5164) -> begin
(

let sz = (getInteger tm_sz.FStar_Syntax_Syntax.n)
in (

let sz_key = (FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz))
in (

let sz_decls = (

let uu____5174 = (FStar_Util.smap_try_find env.cache sz_key)
in (match (uu____5174) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
[]
end
| FStar_Pervasives_Native.None -> begin
(

let t_decls = (FStar_SMTEncoding_Term.mkBvConstructor sz)
in ((

let uu____5182 = (mk_cache_entry env "" [] [])
in (FStar_Util.smap_add env.cache sz_key uu____5182));
t_decls;
))
end))
in (

let uu____5183 = (match (((head1.FStar_Syntax_Syntax.n), (args_e))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5203)::((sz_arg, uu____5205))::(uu____5206)::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) && (isInteger sz_arg.FStar_Syntax_Syntax.n)) -> begin
(

let uu____5255 = (

let uu____5258 = (FStar_List.tail args_e)
in (FStar_List.tail uu____5258))
in (

let uu____5261 = (

let uu____5264 = (getInteger sz_arg.FStar_Syntax_Syntax.n)
in FStar_Pervasives_Native.Some (uu____5264))
in ((uu____5255), (uu____5261))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5270)::((sz_arg, uu____5272))::(uu____5273)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) -> begin
(

let uu____5322 = (

let uu____5323 = (FStar_Syntax_Print.term_to_string sz_arg)
in (FStar_Util.format1 "Not a constant bitvector extend size: %s" uu____5323))
in (failwith uu____5322))
end
| uu____5332 -> begin
(

let uu____5339 = (FStar_List.tail args_e)
in ((uu____5339), (FStar_Pervasives_Native.None)))
end)
in (match (uu____5183) with
| (arg_tms, ext_sz) -> begin
(

let uu____5362 = (encode_args arg_tms env)
in (match (uu____5362) with
| (arg_tms1, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____5383 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms2 -> (

let uu____5392 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5392)))
in (

let unary_arith = (fun arg_tms2 -> (

let uu____5401 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxInt uu____5401)))
in (

let binary = (fun arg_tms2 -> (

let uu____5414 = (

let uu____5415 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5415))
in (

let uu____5416 = (

let uu____5417 = (

let uu____5418 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____5418))
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5417))
in ((uu____5414), (uu____5416)))))
in (

let binary_arith = (fun arg_tms2 -> (

let uu____5433 = (

let uu____5434 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5434))
in (

let uu____5435 = (

let uu____5436 = (

let uu____5437 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____5437))
in (FStar_SMTEncoding_Term.unboxInt uu____5436))
in ((uu____5433), (uu____5435)))))
in (

let mk_bv = (fun op mk_args resBox ts -> (

let uu____5486 = (

let uu____5487 = (mk_args ts)
in (op uu____5487))
in (FStar_All.pipe_right uu____5486 resBox)))
in (

let bv_and = (mk_bv FStar_SMTEncoding_Util.mkBvAnd binary (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_xor = (mk_bv FStar_SMTEncoding_Util.mkBvXor binary (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_or = (mk_bv FStar_SMTEncoding_Util.mkBvOr binary (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_shl = (mk_bv (FStar_SMTEncoding_Util.mkBvShl sz) binary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_shr = (mk_bv (FStar_SMTEncoding_Util.mkBvShr sz) binary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_udiv = (mk_bv (FStar_SMTEncoding_Util.mkBvUdiv sz) binary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_mod = (mk_bv (FStar_SMTEncoding_Util.mkBvMod sz) binary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_mul = (mk_bv (FStar_SMTEncoding_Util.mkBvMul sz) binary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_ult = (mk_bv FStar_SMTEncoding_Util.mkBvUlt binary FStar_SMTEncoding_Term.boxBool)
in (

let bv_uext = (fun arg_tms2 -> (

let uu____5577 = (

let uu____5580 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (FStar_SMTEncoding_Util.mkBvUext uu____5580))
in (

let uu____5582 = (

let uu____5585 = (

let uu____5586 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (sz + uu____5586))
in (FStar_SMTEncoding_Term.boxBitVec uu____5585))
in (mk_bv uu____5577 unary uu____5582 arg_tms2))))
in (

let to_int = (mk_bv FStar_SMTEncoding_Util.mkBvToNat unary FStar_SMTEncoding_Term.boxInt)
in (

let bv_to = (mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz) unary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let ops = (((FStar_Parser_Const.bv_and_lid), (bv_and)))::(((FStar_Parser_Const.bv_xor_lid), (bv_xor)))::(((FStar_Parser_Const.bv_or_lid), (bv_or)))::(((FStar_Parser_Const.bv_shift_left_lid), (bv_shl)))::(((FStar_Parser_Const.bv_shift_right_lid), (bv_shr)))::(((FStar_Parser_Const.bv_udiv_lid), (bv_udiv)))::(((FStar_Parser_Const.bv_mod_lid), (bv_mod)))::(((FStar_Parser_Const.bv_mul_lid), (bv_mul)))::(((FStar_Parser_Const.bv_ult_lid), (bv_ult)))::(((FStar_Parser_Const.bv_uext_lid), (bv_uext)))::(((FStar_Parser_Const.bv_to_nat_lid), (to_int)))::(((FStar_Parser_Const.nat_to_bv_lid), (bv_to)))::[]
in (

let uu____5761 = (

let uu____5770 = (FStar_List.tryFind (fun uu____5792 -> (match (uu____5792) with
| (l, uu____5802) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____5770 FStar_Util.must))
in (match (uu____5761) with
| (uu____5843, op) -> begin
(

let uu____5853 = (op arg_tms1)
in ((uu____5853), ((FStar_List.append sz_decls decls))))
end)))))))))))))))))))))
end))
end)))))
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____5864 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____5864) with
| true -> begin
(

let uu____5865 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____5866 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____5867 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____5865 uu____5866 uu____5867))))
end
| uu____5868 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____5873) -> begin
(

let uu____5898 = (

let uu____5899 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____5900 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____5901 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____5902 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5899 uu____5900 uu____5901 uu____5902)))))
in (failwith uu____5898))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____5907 = (

let uu____5908 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____5909 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____5910 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____5911 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5908 uu____5909 uu____5910 uu____5911)))))
in (failwith uu____5907))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____5917 = (

let uu____5918 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____5918))
in (failwith uu____5917))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, k, uu____5925) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____5967) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t1 = (lookup_term_var env x)
in ((t1), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v1) -> begin
(

let uu____5977 = (lookup_free_var env v1.FStar_Syntax_Syntax.fv_name)
in ((uu____5977), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____5980) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____5984) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(encode_const c env)
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let module_name = env.current_module_name
in (

let uu____6009 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____6009) with
| (binders1, res) -> begin
(

let uu____6020 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____6020) with
| true -> begin
(

let uu____6025 = (encode_binders FStar_Pervasives_Native.None binders1 env)
in (match (uu____6025) with
| (vars, guards, env', decls, uu____6050) -> begin
(

let fsym = (

let uu____6068 = (varops.fresh "f")
in ((uu____6068), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____6071 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___157_6080 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___157_6080.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___157_6080.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___157_6080.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___157_6080.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___157_6080.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___157_6080.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___157_6080.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___157_6080.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___157_6080.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___157_6080.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___157_6080.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___157_6080.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___157_6080.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___157_6080.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___157_6080.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___157_6080.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___157_6080.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___157_6080.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___157_6080.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___157_6080.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___157_6080.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___157_6080.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___157_6080.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___157_6080.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___157_6080.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___157_6080.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___157_6080.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___157_6080.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___157_6080.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.dsenv = uu___157_6080.FStar_TypeChecker_Env.dsenv}) res)
in (match (uu____6071) with
| (pre_opt, res_t) -> begin
(

let uu____6091 = (encode_term_pred FStar_Pervasives_Native.None res_t env' app)
in (match (uu____6091) with
| (res_pred, decls') -> begin
(

let uu____6102 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6115 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____6115), ([])))
end
| FStar_Pervasives_Native.Some (pre) -> begin
(

let uu____6119 = (encode_formula pre env')
in (match (uu____6119) with
| (guard, decls0) -> begin
(

let uu____6132 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____6132), (decls0)))
end))
end)
in (match (uu____6102) with
| (guards1, guard_decls) -> begin
(

let t_interp = (

let uu____6144 = (

let uu____6155 = (FStar_SMTEncoding_Util.mkImp ((guards1), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____6155)))
in (FStar_SMTEncoding_Util.mkForall uu____6144))
in (

let cvars = (

let uu____6173 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____6173 (FStar_List.filter (fun uu____6187 -> (match (uu____6187) with
| (x, uu____6193) -> begin
(Prims.op_disEquality x (FStar_Pervasives_Native.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____6212 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____6212) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____6220 = (

let uu____6221 = (

let uu____6228 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____6228)))
in (FStar_SMTEncoding_Util.mkApp uu____6221))
in ((uu____6220), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append guard_decls (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let tsym = (

let uu____6248 = (

let uu____6249 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____6249))
in (varops.mk_unique uu____6248))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars)
in (

let caption = (

let uu____6260 = (FStar_Options.log_queries ())
in (match (uu____6260) with
| true -> begin
(

let uu____6263 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in FStar_Pervasives_Native.Some (uu____6263))
end
| uu____6264 -> begin
FStar_Pervasives_Native.None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t1 = (

let uu____6271 = (

let uu____6278 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____6278)))
in (FStar_SMTEncoding_Util.mkApp uu____6271))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = (Prims.strcat "kinding_" tsym)
in (

let uu____6290 = (

let uu____6297 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____6297), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____6290)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t1)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t1)
in (

let pre_typing = (

let a_name = (Prims.strcat "pre_typing_" tsym)
in (

let uu____6318 = (

let uu____6325 = (

let uu____6326 = (

let uu____6337 = (

let uu____6338 = (

let uu____6343 = (

let uu____6344 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____6344))
in ((f_has_t), (uu____6343)))
in (FStar_SMTEncoding_Util.mkImp uu____6338))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____6337)))
in (mkForall_fuel uu____6326))
in ((uu____6325), (FStar_Pervasives_Native.Some ("pre-typing for functions")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6318)))
in (

let t_interp1 = (

let a_name = (Prims.strcat "interpretation_" tsym)
in (

let uu____6367 = (

let uu____6374 = (

let uu____6375 = (

let uu____6386 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____6386)))
in (FStar_SMTEncoding_Util.mkForall uu____6375))
in ((uu____6374), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6367)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp1)::[]))))
in ((

let uu____6411 = (mk_cache_entry env tsym cvar_sorts t_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____6411));
((t1), (t_decls));
)))))))))))))
end))))))
end))
end))
end)))))
end))
end
| uu____6414 -> begin
(

let tsym = (varops.fresh "Non_total_Tm_arrow")
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let t1 = (FStar_SMTEncoding_Util.mkApp ((tsym), ([])))
in (

let t_kinding = (

let a_name = (Prims.strcat "non_total_function_typing_" tsym)
in (

let uu____6426 = (

let uu____6433 = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____6433), (FStar_Pervasives_Native.Some ("Typing for non-total arrows")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6426)))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t1)
in (

let t_interp = (

let a_name = (Prims.strcat "pre_typing_" tsym)
in (

let uu____6445 = (

let uu____6452 = (

let uu____6453 = (

let uu____6464 = (

let uu____6465 = (

let uu____6470 = (

let uu____6471 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____6471))
in ((f_has_t), (uu____6470)))
in (FStar_SMTEncoding_Util.mkImp uu____6465))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____6464)))
in (mkForall_fuel uu____6453))
in ((uu____6452), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6445)))
in ((t1), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____6498) -> begin
(

let uu____6505 = (

let uu____6510 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____6510) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.pos = uu____6517; FStar_Syntax_Syntax.vars = uu____6518} -> begin
(

let uu____6525 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____6525) with
| (b, f1) -> begin
(

let uu____6550 = (

let uu____6551 = (FStar_List.hd b)
in (FStar_Pervasives_Native.fst uu____6551))
in ((uu____6550), (f1)))
end))
end
| uu____6560 -> begin
(failwith "impossible")
end))
in (match (uu____6505) with
| (x, f) -> begin
(

let uu____6571 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____6571) with
| (base_t, decls) -> begin
(

let uu____6582 = (gen_term_var env x)
in (match (uu____6582) with
| (x1, xtm, env') -> begin
(

let uu____6596 = (encode_formula f env')
in (match (uu____6596) with
| (refinement, decls') -> begin
(

let uu____6607 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____6607) with
| (fsym, fterm) -> begin
(

let tm_has_type_with_fuel = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (fterm)) xtm base_t)
in (

let encoding = (FStar_SMTEncoding_Util.mkAnd ((tm_has_type_with_fuel), (refinement)))
in (

let cvars = (

let uu____6623 = (

let uu____6626 = (FStar_SMTEncoding_Term.free_variables refinement)
in (

let uu____6633 = (FStar_SMTEncoding_Term.free_variables tm_has_type_with_fuel)
in (FStar_List.append uu____6626 uu____6633)))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____6623))
in (

let cvars1 = (FStar_All.pipe_right cvars (FStar_List.filter (fun uu____6666 -> (match (uu____6666) with
| (y, uu____6672) -> begin
((Prims.op_disEquality y x1) && (Prims.op_disEquality y fsym))
end))))
in (

let xfv = ((x1), (FStar_SMTEncoding_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_SMTEncoding_Term.Fuel_sort))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((ffv)::(xfv)::cvars1), (encoding)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____6705 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____6705) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____6713 = (

let uu____6714 = (

let uu____6721 = (FStar_All.pipe_right cvars1 (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____6721)))
in (FStar_SMTEncoding_Util.mkApp uu____6714))
in ((uu____6713), ((FStar_List.append decls (FStar_List.append decls' (use_cache_entry cache_entry))))))
end
| FStar_Pervasives_Native.None -> begin
(

let module_name = env.current_module_name
in (

let tsym = (

let uu____6742 = (

let uu____6743 = (

let uu____6744 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "_Tm_refine_" uu____6744))
in (Prims.strcat module_name uu____6743))
in (varops.mk_unique uu____6742))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars1)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let t1 = (

let uu____6758 = (

let uu____6765 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((tsym), (uu____6765)))
in (FStar_SMTEncoding_Util.mkApp uu____6758))
in (

let x_has_base_t = (FStar_SMTEncoding_Term.mk_HasType xtm base_t)
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (fterm)) xtm t1)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t1)
in (

let t_haseq1 = (

let uu____6780 = (

let uu____6787 = (

let uu____6788 = (

let uu____6799 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars1), (uu____6799)))
in (FStar_SMTEncoding_Util.mkForall uu____6788))
in ((uu____6787), (FStar_Pervasives_Native.Some ((Prims.strcat "haseq for " tsym))), ((Prims.strcat "haseq" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____6780))
in (

let t_valid = (

let xx = ((x1), (FStar_SMTEncoding_Term.Term_sort))
in (

let valid_t = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((t1)::[])))
in (

let uu____6825 = (

let uu____6832 = (

let uu____6833 = (

let uu____6844 = (

let uu____6845 = (

let uu____6850 = (

let uu____6851 = (

let uu____6862 = (FStar_SMTEncoding_Util.mkAnd ((x_has_base_t), (refinement)))
in (([]), ((xx)::[]), (uu____6862)))
in (FStar_SMTEncoding_Util.mkExists uu____6851))
in ((uu____6850), (valid_t)))
in (FStar_SMTEncoding_Util.mkIff uu____6845))
in ((((valid_t)::[])::[]), (cvars1), (uu____6844)))
in (FStar_SMTEncoding_Util.mkForall uu____6833))
in ((uu____6832), (FStar_Pervasives_Native.Some ("validity axiom for refinement")), ((Prims.strcat "ref_valid_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____6825))))
in (

let t_kinding = (

let uu____6900 = (

let uu____6907 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars1), (t_has_kind)))
in ((uu____6907), (FStar_Pervasives_Native.Some ("refinement kinding")), ((Prims.strcat "refinement_kinding_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____6900))
in (

let t_interp = (

let uu____6925 = (

let uu____6932 = (

let uu____6933 = (

let uu____6944 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars1), (uu____6944)))
in (FStar_SMTEncoding_Util.mkForall uu____6933))
in (

let uu____6967 = (

let uu____6970 = (FStar_Syntax_Print.term_to_string t0)
in FStar_Pervasives_Native.Some (uu____6970))
in ((uu____6932), (uu____6967), ((Prims.strcat "refinement_interpretation_" tsym)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6925))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_valid)::(t_interp)::(t_haseq1)::[])))
in ((

let uu____6977 = (mk_cache_entry env tsym cvar_sorts t_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____6977));
((t1), (t_decls));
))))))))))))))))
end))))))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(

let ttm = (

let uu____7007 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____7007))
in (

let uu____7008 = (encode_term_pred FStar_Pervasives_Native.None k env ttm)
in (match (uu____7008) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____7020 = (

let uu____7027 = (

let uu____7028 = (

let uu____7029 = (

let uu____7030 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____7030))
in (FStar_Util.format1 "uvar_typing_%s" uu____7029))
in (varops.mk_unique uu____7028))
in ((t_has_k), (FStar_Pervasives_Native.Some ("Uvar typing")), (uu____7027)))
in (FStar_SMTEncoding_Util.mkAssume uu____7020))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____7035) -> begin
(

let uu____7050 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____7050) with
| (head1, args_e) -> begin
(

let uu____7091 = (

let uu____7104 = (

let uu____7105 = (FStar_Syntax_Subst.compress head1)
in uu____7105.FStar_Syntax_Syntax.n)
in ((uu____7104), (args_e)))
in (match (uu____7091) with
| uu____7120 when (head_redex env head1) -> begin
(

let uu____7133 = (whnf env t)
in (encode_term uu____7133 env))
end
| uu____7134 when (is_arithmetic_primitive head1 args_e) -> begin
(encode_arith_term env head1 args_e)
end
| uu____7153 when (is_BitVector_primitive head1 args_e) -> begin
(encode_BitVector_term env head1 args_e)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7167; FStar_Syntax_Syntax.vars = uu____7168}, uu____7169), (uu____7170)::((v1, uu____7172))::((v2, uu____7174))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7225 = (encode_term v1 env)
in (match (uu____7225) with
| (v11, decls1) -> begin
(

let uu____7236 = (encode_term v2 env)
in (match (uu____7236) with
| (v21, decls2) -> begin
(

let uu____7247 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7247), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____7251)::((v1, uu____7253))::((v2, uu____7255))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7302 = (encode_term v1 env)
in (match (uu____7302) with
| (v11, decls1) -> begin
(

let uu____7313 = (encode_term v2 env)
in (match (uu____7313) with
| (v21, decls2) -> begin
(

let uu____7324 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7324), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____7327) -> begin
(

let e0 = (

let uu____7345 = (FStar_List.hd args_e)
in (FStar_TypeChecker_Util.reify_body_with_arg env.tcenv head1 uu____7345))
in ((

let uu____7353 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____7353) with
| true -> begin
(

let uu____7354 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" uu____7354))
end
| uu____7355 -> begin
()
end));
(

let e = (

let uu____7359 = (

let uu____7360 = (FStar_TypeChecker_Util.remove_reify e0)
in (

let uu____7361 = (FStar_List.tl args_e)
in (FStar_Syntax_Syntax.mk_Tm_app uu____7360 uu____7361)))
in (uu____7359 FStar_Pervasives_Native.None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____7370)), ((arg, uu____7372))::[]) -> begin
(encode_term arg env)
end
| uu____7397 -> begin
(

let uu____7410 = (encode_args args_e env)
in (match (uu____7410) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____7465 = (encode_term head1 env)
in (match (uu____7465) with
| (head2, decls') -> begin
(

let app_tm = (mk_Apply_args head2 args)
in (match (ht_opt) with
| FStar_Pervasives_Native.None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| FStar_Pervasives_Native.Some (formals, c) -> begin
(

let uu____7529 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____7529) with
| (formals1, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____7607 uu____7608 -> (match (((uu____7607), (uu____7608))) with
| ((bv, uu____7630), (a, uu____7632)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals1 args_e)
in (

let ty = (

let uu____7650 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____7650 (FStar_Syntax_Subst.subst subst1)))
in (

let uu____7655 = (encode_term_pred FStar_Pervasives_Native.None ty env app_tm)
in (match (uu____7655) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____7670 = (

let uu____7677 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____7686 = (

let uu____7687 = (

let uu____7688 = (

let uu____7689 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____7689))
in (Prims.strcat "partial_app_typing_" uu____7688))
in (varops.mk_unique uu____7687))
in ((uu____7677), (FStar_Pervasives_Native.Some ("Partial app typing")), (uu____7686))))
in (FStar_SMTEncoding_Util.mkAssume uu____7670))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____7706 = (lookup_free_var_sym env fv)
in (match (uu____7706) with
| (fname, fuel_args) -> begin
(

let tm = (FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args args))))
in ((tm), (decls)))
end)))
in (

let head2 = (FStar_Syntax_Subst.compress head1)
in (

let head_type = (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.pos = uu____7737; FStar_Syntax_Syntax.vars = uu____7738}, uu____7739) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7750; FStar_Syntax_Syntax.vars = uu____7751}, uu____7752) -> begin
(

let uu____7757 = (

let uu____7758 = (

let uu____7763 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____7763 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7758 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____7757))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____7793 = (

let uu____7794 = (

let uu____7799 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____7799 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7794 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____7793))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____7828, (FStar_Util.Inl (t1), uu____7830), uu____7831) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____7880, (FStar_Util.Inr (c), uu____7882), uu____7883) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| uu____7932 -> begin
FStar_Pervasives_Native.None
end)
in (match (head_type) with
| FStar_Pervasives_Native.None -> begin
(encode_partial_app FStar_Pervasives_Native.None)
end
| FStar_Pervasives_Native.Some (head_type1) -> begin
(

let head_type2 = (

let uu____7959 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____7959))
in (

let uu____7960 = (curried_arrow_formals_comp head_type2)
in (match (uu____7960) with
| (formals, c) -> begin
(match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7976; FStar_Syntax_Syntax.vars = uu____7977}, uu____7978) when (Prims.op_Equality (FStar_List.length formals) (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (Prims.op_Equality (FStar_List.length formals) (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____7992 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (FStar_Pervasives_Native.Some (((formals), (c)))))
end
| uu____8005 -> begin
(encode_partial_app FStar_Pervasives_Native.None)
end)
end)
end)))
end)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let uu____8041 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____8041) with
| (bs1, body1, opening) -> begin
(

let fallback = (fun uu____8064 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Imprecise function encoding"))))
in (

let uu____8071 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____8071), ((decl)::[]))))))
in (

let is_impure = (fun rc -> (

let uu____8078 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv rc.FStar_Syntax_Syntax.residual_effect)
in (FStar_All.pipe_right uu____8078 Prims.op_Negation)))
in (

let codomain_eff = (fun rc -> (

let res_typ = (match (rc.FStar_Syntax_Syntax.residual_typ) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8088 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____8088 FStar_Pervasives_Native.fst))
end
| FStar_Pervasives_Native.Some (t1) -> begin
t1
end)
in (match ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(

let uu____8108 = (FStar_Syntax_Syntax.mk_Total res_typ)
in FStar_Pervasives_Native.Some (uu____8108))
end
| uu____8109 -> begin
(match ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(

let uu____8112 = (FStar_Syntax_Syntax.mk_GTotal res_typ)
in FStar_Pervasives_Native.Some (uu____8112))
end
| uu____8113 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (lopt) with
| FStar_Pervasives_Native.None -> begin
((

let uu____8119 = (

let uu____8120 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____8120))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____8119));
(fallback ());
)
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____8122 = ((is_impure rc) && (

let uu____8124 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (not (uu____8124))))
in (match (uu____8122) with
| true -> begin
(fallback ())
end
| uu____8129 -> begin
(

let cache_size = (FStar_Util.smap_size env.cache)
in (

let uu____8131 = (encode_binders FStar_Pervasives_Native.None bs1 env)
in (match (uu____8131) with
| (vars, guards, envbody, decls, uu____8156) -> begin
(

let body2 = (

let uu____8170 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (match (uu____8170) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.tcenv body1)
end
| uu____8171 -> begin
body1
end))
in (

let uu____8172 = (encode_term body2 envbody)
in (match (uu____8172) with
| (body3, decls') -> begin
(

let uu____8183 = (

let uu____8192 = (codomain_eff rc)
in (match (uu____8192) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), ([]))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs1 c)
in (

let uu____8211 = (encode_term tfun env)
in (match (uu____8211) with
| (t1, decls1) -> begin
((FStar_Pervasives_Native.Some (t1)), (decls1))
end)))
end))
in (match (uu____8183) with
| (arrow_t_opt, decls'') -> begin
(

let key_body = (

let uu____8243 = (

let uu____8254 = (

let uu____8255 = (

let uu____8260 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____8260), (body3)))
in (FStar_SMTEncoding_Util.mkImp uu____8255))
in (([]), (vars), (uu____8254)))
in (FStar_SMTEncoding_Util.mkForall uu____8243))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let cvars1 = (match (arrow_t_opt) with
| FStar_Pervasives_Native.None -> begin
cvars
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____8272 = (

let uu____8275 = (FStar_SMTEncoding_Term.free_variables t1)
in (FStar_List.append uu____8275 cvars))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____8272))
end)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars1), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____8294 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____8294) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____8302 = (

let uu____8303 = (

let uu____8310 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((cache_entry.cache_symbol_name), (uu____8310)))
in (FStar_SMTEncoding_Util.mkApp uu____8303))
in ((uu____8302), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8321 = (is_an_eta_expansion env vars body3)
in (match (uu____8321) with
| FStar_Pervasives_Native.Some (t1) -> begin
(

let decls1 = (

let uu____8332 = (

let uu____8333 = (FStar_Util.smap_size env.cache)
in (Prims.op_Equality uu____8333 cache_size))
in (match (uu____8332) with
| true -> begin
[]
end
| uu____8336 -> begin
(FStar_List.append decls (FStar_List.append decls' decls''))
end))
in ((t1), (decls1)))
end
| FStar_Pervasives_Native.None -> begin
(

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars1)
in (

let fsym = (

let module_name = env.current_module_name
in (

let fsym = (

let uu____8349 = (

let uu____8350 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____8350))
in (varops.mk_unique uu____8349))
in (Prims.strcat module_name (Prims.strcat "_" fsym))))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let f = (

let uu____8357 = (

let uu____8364 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((fsym), (uu____8364)))
in (FStar_SMTEncoding_Util.mkApp uu____8357))
in (

let app = (mk_Apply f vars)
in (

let typing_f = (match (arrow_t_opt) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let f_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel FStar_Pervasives_Native.None f t1)
in (

let a_name = (Prims.strcat "typing_" fsym)
in (

let uu____8382 = (

let uu____8383 = (

let uu____8390 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars1), (f_has_t)))
in ((uu____8390), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____8383))
in (uu____8382)::[])))
end)
in (

let interp_f = (

let a_name = (Prims.strcat "interpretation_" fsym)
in (

let uu____8403 = (

let uu____8410 = (

let uu____8411 = (

let uu____8422 = (FStar_SMTEncoding_Util.mkEq ((app), (body3)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars1)), (uu____8422)))
in (FStar_SMTEncoding_Util.mkForall uu____8411))
in ((uu____8410), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____8403)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[])))))
in ((

let uu____8439 = (mk_cache_entry env fsym cvar_sorts f_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____8439));
((f), (f_decls));
)))))))))
end))
end)))))))
end))
end)))
end)))
end))
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((uu____8442, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____8443); FStar_Syntax_Syntax.lbunivs = uu____8444; FStar_Syntax_Syntax.lbtyp = uu____8445; FStar_Syntax_Syntax.lbeff = uu____8446; FStar_Syntax_Syntax.lbdef = uu____8447})::uu____8448), uu____8449) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____8475; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____8477; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____8498) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(FStar_Exn.raise Inner_let_rec);
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____8568 = (encode_term e1 env)
in (match (uu____8568) with
| (ee1, decls1) -> begin
(

let uu____8579 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) e2)
in (match (uu____8579) with
| (xs, e21) -> begin
(

let uu____8604 = (FStar_List.hd xs)
in (match (uu____8604) with
| (x1, uu____8618) -> begin
(

let env' = (push_term_var env x1 ee1)
in (

let uu____8620 = (encode_body e21 env')
in (match (uu____8620) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____8652 = (

let uu____8659 = (

let uu____8660 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_bv uu____8660))
in (gen_term_var env uu____8659))
in (match (uu____8652) with
| (scrsym, scr', env1) -> begin
(

let uu____8668 = (encode_term e env1)
in (match (uu____8668) with
| (scr, decls) -> begin
(

let uu____8679 = (

let encode_branch = (fun b uu____8704 -> (match (uu____8704) with
| (else_case, decls1) -> begin
(

let uu____8723 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____8723) with
| (p, w, br) -> begin
(

let uu____8749 = (encode_pat env1 p)
in (match (uu____8749) with
| (env0, pattern) -> begin
(

let guard = (pattern.guard scr')
in (

let projections = (pattern.projections scr')
in (

let env2 = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env2 uu____8786 -> (match (uu____8786) with
| (x, t) -> begin
(push_term_var env2 x t)
end)) env1))
in (

let uu____8793 = (match (w) with
| FStar_Pervasives_Native.None -> begin
((guard), ([]))
end
| FStar_Pervasives_Native.Some (w1) -> begin
(

let uu____8815 = (encode_term w1 env2)
in (match (uu____8815) with
| (w2, decls2) -> begin
(

let uu____8828 = (

let uu____8829 = (

let uu____8834 = (

let uu____8835 = (

let uu____8840 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w2), (uu____8840)))
in (FStar_SMTEncoding_Util.mkEq uu____8835))
in ((guard), (uu____8834)))
in (FStar_SMTEncoding_Util.mkAnd uu____8829))
in ((uu____8828), (decls2)))
end))
end)
in (match (uu____8793) with
| (guard1, decls2) -> begin
(

let uu____8853 = (encode_br br env2)
in (match (uu____8853) with
| (br1, decls3) -> begin
(

let uu____8866 = (FStar_SMTEncoding_Util.mkITE ((guard1), (br1), (else_case)))
in ((uu____8866), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end)))))
end))
end))
end))
in (FStar_List.fold_right encode_branch pats ((default_case), (decls))))
in (match (uu____8679) with
| (match_tm, decls1) -> begin
(

let uu____8885 = (FStar_SMTEncoding_Term.mkLet' (((((((scrsym), (FStar_SMTEncoding_Term.Term_sort))), (scr)))::[]), (match_tm)) FStar_Range.dummyRange)
in ((uu____8885), (decls1)))
end))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____8925 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____8925) with
| true -> begin
(

let uu____8926 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____8926))
end
| uu____8927 -> begin
()
end));
(

let uu____8928 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____8928) with
| (vars, pat_term) -> begin
(

let uu____8945 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____8998 v1 -> (match (uu____8998) with
| (env1, vars1) -> begin
(

let uu____9050 = (gen_term_var env1 v1)
in (match (uu____9050) with
| (xx, uu____9072, env2) -> begin
((env2), ((((v1), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars1))
end))
end)) ((env), ([]))))
in (match (uu____8945) with
| (env1, vars1) -> begin
(

let rec mk_guard = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (uu____9151) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_wild (uu____9152) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____9153) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____9161 = (encode_const c env1)
in (match (uu____9161) with
| (tm, decls) -> begin
((match (decls) with
| (uu____9175)::uu____9176 -> begin
(failwith "Unexpected encoding of constant pattern")
end
| uu____9179 -> begin
()
end);
(FStar_SMTEncoding_Util.mkEq ((scrutinee), (tm)));
)
end))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (

let tc_name = (FStar_TypeChecker_Env.typ_of_datacon env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____9202 = (FStar_TypeChecker_Env.datacons_of_typ env1.tcenv tc_name)
in (match (uu____9202) with
| (uu____9209, (uu____9210)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____9213 -> begin
(mk_data_tester env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
end)))
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____9246 -> (match (uu____9246) with
| (arg, uu____9254) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____9260 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____9260)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____9287) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____9318) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____9341 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____9385 -> (match (uu____9385) with
| (arg, uu____9399) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____9405 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____9405)))
end))))
in (FStar_All.pipe_right uu____9341 FStar_List.flatten))
end))
in (

let pat_term1 = (fun uu____9433 -> (encode_term pat_term env1))
in (

let pattern = {pat_vars = vars1; pat_term = pat_term1; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env1), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____9443 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____9481 uu____9482 -> (match (((uu____9481), (uu____9482))) with
| ((tms, decls), (t, uu____9518)) -> begin
(

let uu____9539 = (encode_term t env)
in (match (uu____9539) with
| (t1, decls') -> begin
(((t1)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____9443) with
| (l1, decls) -> begin
(((FStar_List.rev l1)), (decls))
end)))
and encode_function_type_as_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let list_elements1 = (fun e -> (

let uu____9596 = (FStar_Syntax_Util.list_elements e)
in (match (uu____9596) with
| FStar_Pervasives_Native.Some (l) -> begin
l
end
| FStar_Pervasives_Native.None -> begin
((FStar_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern");
[];
)
end)))
in (

let one_pat = (fun p -> (

let uu____9617 = (

let uu____9632 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____9632 FStar_Syntax_Util.head_and_args))
in (match (uu____9617) with
| (head1, args) -> begin
(

let uu____9671 = (

let uu____9684 = (

let uu____9685 = (FStar_Syntax_Util.un_uinst head1)
in uu____9685.FStar_Syntax_Syntax.n)
in ((uu____9684), (args)))
in (match (uu____9671) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____9699, uu____9700))::((e, uu____9702))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
e
end
| uu____9737 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements1 p)
in (

let smt_pat_or1 = (fun t1 -> (

let uu____9773 = (

let uu____9788 = (FStar_Syntax_Util.unmeta t1)
in (FStar_All.pipe_right uu____9788 FStar_Syntax_Util.head_and_args))
in (match (uu____9773) with
| (head1, args) -> begin
(

let uu____9829 = (

let uu____9842 = (

let uu____9843 = (FStar_Syntax_Util.un_uinst head1)
in uu____9843.FStar_Syntax_Syntax.n)
in ((uu____9842), (args)))
in (match (uu____9829) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____9860))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
FStar_Pervasives_Native.Some (e)
end
| uu____9887 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (elts) with
| (t1)::[] -> begin
(

let uu____9909 = (smt_pat_or1 t1)
in (match (uu____9909) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____9925 = (list_elements1 e)
in (FStar_All.pipe_right uu____9925 (FStar_List.map (fun branch1 -> (

let uu____9943 = (list_elements1 branch1)
in (FStar_All.pipe_right uu____9943 (FStar_List.map one_pat)))))))
end
| uu____9954 -> begin
(

let uu____9959 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____9959)::[])
end))
end
| uu____9980 -> begin
(

let uu____9983 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____9983)::[])
end))))
in (

let uu____10004 = (

let uu____10023 = (

let uu____10024 = (FStar_Syntax_Subst.compress t)
in uu____10024.FStar_Syntax_Syntax.n)
in (match (uu____10023) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____10063 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____10063) with
| (binders1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____10106; FStar_Syntax_Syntax.effect_name = uu____10107; FStar_Syntax_Syntax.result_typ = uu____10108; FStar_Syntax_Syntax.effect_args = ((pre, uu____10110))::((post, uu____10112))::((pats, uu____10114))::[]; FStar_Syntax_Syntax.flags = uu____10115}) -> begin
(

let uu____10156 = (lemma_pats pats)
in ((binders1), (pre), (post), (uu____10156)))
end
| uu____10173 -> begin
(failwith "impos")
end)
end))
end
| uu____10192 -> begin
(failwith "Impos")
end))
in (match (uu____10004) with
| (binders, pre, post, patterns) -> begin
(

let env1 = (

let uu___158_10240 = env
in {bindings = uu___158_10240.bindings; depth = uu___158_10240.depth; tcenv = uu___158_10240.tcenv; warn = uu___158_10240.warn; cache = uu___158_10240.cache; nolabels = uu___158_10240.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___158_10240.encode_non_total_function_typ; current_module_name = uu___158_10240.current_module_name})
in (

let uu____10241 = (encode_binders FStar_Pervasives_Native.None binders env1)
in (match (uu____10241) with
| (vars, guards, env2, decls, uu____10266) -> begin
(

let uu____10279 = (

let uu____10292 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch1 -> (

let uu____10336 = (

let uu____10345 = (FStar_All.pipe_right branch1 (FStar_List.map (fun t1 -> (encode_term t1 env2))))
in (FStar_All.pipe_right uu____10345 FStar_List.unzip))
in (match (uu____10336) with
| (pats, decls1) -> begin
((pats), (decls1))
end)))))
in (FStar_All.pipe_right uu____10292 FStar_List.unzip))
in (match (uu____10279) with
| (pats, decls') -> begin
(

let decls'1 = (FStar_List.flatten decls')
in (

let env3 = (

let uu___159_10454 = env2
in {bindings = uu___159_10454.bindings; depth = uu___159_10454.depth; tcenv = uu___159_10454.tcenv; warn = uu___159_10454.warn; cache = uu___159_10454.cache; nolabels = true; use_zfuel_name = uu___159_10454.use_zfuel_name; encode_non_total_function_typ = uu___159_10454.encode_non_total_function_typ; current_module_name = uu___159_10454.current_module_name})
in (

let uu____10455 = (

let uu____10460 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____10460 env3))
in (match (uu____10455) with
| (pre1, decls'') -> begin
(

let uu____10467 = (

let uu____10472 = (FStar_Syntax_Util.unmeta post)
in (encode_formula uu____10472 env3))
in (match (uu____10467) with
| (post1, decls''') -> begin
(

let decls1 = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls'1) (FStar_List.append decls'' decls''')))
in (

let uu____10482 = (

let uu____10483 = (

let uu____10494 = (

let uu____10495 = (

let uu____10500 = (FStar_SMTEncoding_Util.mk_and_l ((pre1)::guards))
in ((uu____10500), (post1)))
in (FStar_SMTEncoding_Util.mkImp uu____10495))
in ((pats), (vars), (uu____10494)))
in (FStar_SMTEncoding_Util.mkForall uu____10483))
in ((uu____10482), (decls1))))
end))
end))))
end))
end)))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug1 = (fun phi1 -> (

let uu____10519 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____10519) with
| true -> begin
(

let uu____10520 = (FStar_Syntax_Print.tag_of_term phi1)
in (

let uu____10521 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____10520 uu____10521)))
end
| uu____10522 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____10554 = (FStar_Util.fold_map (fun decls x -> (

let uu____10582 = (encode_term (FStar_Pervasives_Native.fst x) env)
in (match (uu____10582) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____10554) with
| (decls, args) -> begin
(

let uu____10611 = (

let uu___160_10612 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___160_10612.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___160_10612.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____10611), (decls)))
end)))
in (

let const_op = (fun f r uu____10643 -> (

let uu____10656 = (f r)
in ((uu____10656), ([]))))
in (

let un_op = (fun f l -> (

let uu____10675 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____10675)))
in (

let bin_op = (fun f uu___134_10691 -> (match (uu___134_10691) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____10702 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____10736 = (FStar_Util.fold_map (fun decls uu____10759 -> (match (uu____10759) with
| (t, uu____10773) -> begin
(

let uu____10774 = (encode_formula t env)
in (match (uu____10774) with
| (phi1, decls') -> begin
(((FStar_List.append decls decls')), (phi1))
end))
end)) [] l)
in (match (uu____10736) with
| (decls, phis) -> begin
(

let uu____10803 = (

let uu___161_10804 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___161_10804.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___161_10804.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____10803), (decls)))
end)))
in (

let eq_op = (fun r args -> (

let rf = (FStar_List.filter (fun uu____10865 -> (match (uu____10865) with
| (a, q) -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10884)) -> begin
false
end
| uu____10885 -> begin
true
end)
end)) args)
in (match ((Prims.op_disEquality (FStar_List.length rf) (Prims.parse_int "2"))) with
| true -> begin
(

let uu____10900 = (FStar_Util.format1 "eq_op: got %s non-implicit arguments instead of 2?" (Prims.string_of_int (FStar_List.length rf)))
in (failwith uu____10900))
end
| uu____10913 -> begin
(

let uu____10914 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____10914 r rf))
end)))
in (

let mk_imp1 = (fun r uu___135_10939 -> (match (uu___135_10939) with
| ((lhs, uu____10945))::((rhs, uu____10947))::[] -> begin
(

let uu____10974 = (encode_formula rhs env)
in (match (uu____10974) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____10989) -> begin
((l1), (decls1))
end
| uu____10994 -> begin
(

let uu____10995 = (encode_formula lhs env)
in (match (uu____10995) with
| (l2, decls2) -> begin
(

let uu____11006 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____11006), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____11009 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___136_11030 -> (match (uu___136_11030) with
| ((guard, uu____11036))::((_then, uu____11038))::((_else, uu____11040))::[] -> begin
(

let uu____11077 = (encode_formula guard env)
in (match (uu____11077) with
| (g, decls1) -> begin
(

let uu____11088 = (encode_formula _then env)
in (match (uu____11088) with
| (t, decls2) -> begin
(

let uu____11099 = (encode_formula _else env)
in (match (uu____11099) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____11113 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____11138 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____11138)))
in (

let connectives = (

let uu____11156 = (

let uu____11169 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Parser_Const.and_lid), (uu____11169)))
in (

let uu____11186 = (

let uu____11201 = (

let uu____11214 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Parser_Const.or_lid), (uu____11214)))
in (

let uu____11231 = (

let uu____11246 = (

let uu____11261 = (

let uu____11274 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Parser_Const.iff_lid), (uu____11274)))
in (

let uu____11291 = (

let uu____11306 = (

let uu____11321 = (

let uu____11334 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Parser_Const.not_lid), (uu____11334)))
in (uu____11321)::(((FStar_Parser_Const.eq2_lid), (eq_op)))::(((FStar_Parser_Const.eq3_lid), (eq_op)))::(((FStar_Parser_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Parser_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Parser_Const.ite_lid), (mk_ite)))::uu____11306)
in (uu____11261)::uu____11291))
in (((FStar_Parser_Const.imp_lid), (mk_imp1)))::uu____11246)
in (uu____11201)::uu____11231))
in (uu____11156)::uu____11186))
in (

let rec fallback = (fun phi1 -> (match (phi1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____11655 = (encode_formula phi' env)
in (match (uu____11655) with
| (phi2, decls) -> begin
(

let uu____11666 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi2), (msg), (r)))) r)
in ((uu____11666), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____11667) -> begin
(

let uu____11674 = (FStar_Syntax_Util.unmeta phi1)
in (encode_formula uu____11674 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____11713 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____11713) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____11725; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____11727; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____11748 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____11748) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____11795)::((x, uu____11797))::((t, uu____11799))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid) -> begin
(

let uu____11846 = (encode_term x env)
in (match (uu____11846) with
| (x1, decls) -> begin
(

let uu____11857 = (encode_term t env)
in (match (uu____11857) with
| (t1, decls') -> begin
(

let uu____11868 = (FStar_SMTEncoding_Term.mk_HasType x1 t1)
in ((uu____11868), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____11873))::((msg, uu____11875))::((phi2, uu____11877))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.labeled_lid) -> begin
(

let uu____11922 = (

let uu____11927 = (

let uu____11928 = (FStar_Syntax_Subst.compress r)
in uu____11928.FStar_Syntax_Syntax.n)
in (

let uu____11931 = (

let uu____11932 = (FStar_Syntax_Subst.compress msg)
in uu____11932.FStar_Syntax_Syntax.n)
in ((uu____11927), (uu____11931))))
in (match (uu____11922) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____11941))) -> begin
(

let phi3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi2), (FStar_Syntax_Syntax.Meta_labeled (((s), (r1), (false))))))) FStar_Pervasives_Native.None r1)
in (fallback phi3))
end
| uu____11947 -> begin
(fallback phi2)
end))
end
| uu____11952 when (head_redex env head2) -> begin
(

let uu____11965 = (whnf env phi1)
in (encode_formula uu____11965 env))
end
| uu____11966 -> begin
(

let uu____11979 = (encode_term phi1 env)
in (match (uu____11979) with
| (tt, decls) -> begin
(

let uu____11990 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___162_11993 = tt
in {FStar_SMTEncoding_Term.tm = uu___162_11993.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___162_11993.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____11990), (decls)))
end))
end))
end
| uu____11994 -> begin
(

let uu____11995 = (encode_term phi1 env)
in (match (uu____11995) with
| (tt, decls) -> begin
(

let uu____12006 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___163_12009 = tt
in {FStar_SMTEncoding_Term.tm = uu___163_12009.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___163_12009.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____12006), (decls)))
end))
end))
in (

let encode_q_body = (fun env1 bs ps body -> (

let uu____12045 = (encode_binders FStar_Pervasives_Native.None bs env1)
in (match (uu____12045) with
| (vars, guards, env2, decls, uu____12084) -> begin
(

let uu____12097 = (

let uu____12110 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____12158 = (

let uu____12167 = (FStar_All.pipe_right p (FStar_List.map (fun uu____12197 -> (match (uu____12197) with
| (t, uu____12207) -> begin
(encode_term t (

let uu___164_12209 = env2
in {bindings = uu___164_12209.bindings; depth = uu___164_12209.depth; tcenv = uu___164_12209.tcenv; warn = uu___164_12209.warn; cache = uu___164_12209.cache; nolabels = uu___164_12209.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___164_12209.encode_non_total_function_typ; current_module_name = uu___164_12209.current_module_name}))
end))))
in (FStar_All.pipe_right uu____12167 FStar_List.unzip))
in (match (uu____12158) with
| (p1, decls1) -> begin
((p1), ((FStar_List.flatten decls1)))
end)))))
in (FStar_All.pipe_right uu____12110 FStar_List.unzip))
in (match (uu____12097) with
| (pats, decls') -> begin
(

let uu____12308 = (encode_formula body env2)
in (match (uu____12308) with
| (body1, decls'') -> begin
(

let guards1 = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____12340; FStar_SMTEncoding_Term.rng = uu____12341})::[])::[] when (Prims.op_Equality (FStar_Ident.text_of_lid FStar_Parser_Const.guard_free) gf) -> begin
[]
end
| uu____12356 -> begin
guards
end)
in (

let uu____12361 = (FStar_SMTEncoding_Util.mk_and_l guards1)
in ((vars), (pats), (uu____12361), (body1), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug1 phi);
(

let phi1 = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____12421 -> (match (uu____12421) with
| (x, uu____12427) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats1) with
| [] -> begin
()
end
| (hd1)::tl1 -> begin
(

let pat_vars = (

let uu____12435 = (FStar_Syntax_Free.names hd1)
in (FStar_List.fold_left (fun out x -> (

let uu____12447 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____12447))) uu____12435 tl1))
in (

let uu____12450 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____12477 -> (match (uu____12477) with
| (b, uu____12483) -> begin
(

let uu____12484 = (FStar_Util.set_mem b pat_vars)
in (not (uu____12484)))
end))))
in (match (uu____12450) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____12490) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd1.FStar_Syntax_Syntax.pos tl1)
in (

let uu____12504 = (

let uu____12505 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____12505))
in (FStar_Errors.warn pos uu____12504)))
end)))
end)))
in (

let uu____12506 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____12506) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____12515 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____12573 -> (match (uu____12573) with
| (l, uu____12587) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____12515) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (uu____12620, f) -> begin
(f phi1.FStar_Syntax_Syntax.pos arms)
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____12660 = (encode_q_body env vars pats body)
in (match (uu____12660) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let tm = (

let uu____12705 = (

let uu____12716 = (FStar_SMTEncoding_Util.mkImp ((guard), (body1)))
in ((pats1), (vars1), (uu____12716)))
in (FStar_SMTEncoding_Term.mkForall uu____12705 phi1.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____12735 = (encode_q_body env vars pats body)
in (match (uu____12735) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let uu____12779 = (

let uu____12780 = (

let uu____12791 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body1)))
in ((pats1), (vars1), (uu____12791)))
in (FStar_SMTEncoding_Term.mkExists uu____12780 phi1.FStar_Syntax_Syntax.pos))
in ((uu____12779), (decls)))
end));
)
end))));
)))))))))))))))

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let __proj__Mkprims_t__item__mk : prims_t  ->  FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun projectee -> (match (projectee) with
| {mk = __fname__mk; is = __fname__is} -> begin
__fname__mk
end))


let __proj__Mkprims_t__item__is : prims_t  ->  FStar_Ident.lident  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {mk = __fname__mk; is = __fname__is} -> begin
__fname__is
end))


let prims : prims_t = (

let uu____12889 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____12889) with
| (asym, a) -> begin
(

let uu____12896 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____12896) with
| (xsym, x) -> begin
(

let uu____12903 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____12903) with
| (ysym, y) -> begin
(

let quant = (fun vars body x1 -> (

let xname_decl = (

let uu____12947 = (

let uu____12958 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in ((x1), (uu____12958), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____12947))
in (

let xtok = (Prims.strcat x1 "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let xapp = (

let uu____12984 = (

let uu____12991 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x1), (uu____12991)))
in (FStar_SMTEncoding_Util.mkApp uu____12984))
in (

let xtok1 = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok1 vars)
in (

let uu____13004 = (

let uu____13007 = (

let uu____13010 = (

let uu____13013 = (

let uu____13014 = (

let uu____13021 = (

let uu____13022 = (

let uu____13033 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____13033)))
in (FStar_SMTEncoding_Util.mkForall uu____13022))
in ((uu____13021), (FStar_Pervasives_Native.None), ((Prims.strcat "primitive_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____13014))
in (

let uu____13050 = (

let uu____13053 = (

let uu____13054 = (

let uu____13061 = (

let uu____13062 = (

let uu____13073 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____13073)))
in (FStar_SMTEncoding_Util.mkForall uu____13062))
in ((uu____13061), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____13054))
in (uu____13053)::[])
in (uu____13013)::uu____13050))
in (xtok_decl)::uu____13010)
in (xname_decl)::uu____13007)
in ((xtok1), (uu____13004))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims1 = (

let uu____13164 = (

let uu____13177 = (

let uu____13186 = (

let uu____13187 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13187))
in (quant axy uu____13186))
in ((FStar_Parser_Const.op_Eq), (uu____13177)))
in (

let uu____13196 = (

let uu____13211 = (

let uu____13224 = (

let uu____13233 = (

let uu____13234 = (

let uu____13235 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____13235))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13234))
in (quant axy uu____13233))
in ((FStar_Parser_Const.op_notEq), (uu____13224)))
in (

let uu____13244 = (

let uu____13259 = (

let uu____13272 = (

let uu____13281 = (

let uu____13282 = (

let uu____13283 = (

let uu____13288 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13289 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13288), (uu____13289))))
in (FStar_SMTEncoding_Util.mkLT uu____13283))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13282))
in (quant xy uu____13281))
in ((FStar_Parser_Const.op_LT), (uu____13272)))
in (

let uu____13298 = (

let uu____13313 = (

let uu____13326 = (

let uu____13335 = (

let uu____13336 = (

let uu____13337 = (

let uu____13342 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13343 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13342), (uu____13343))))
in (FStar_SMTEncoding_Util.mkLTE uu____13337))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13336))
in (quant xy uu____13335))
in ((FStar_Parser_Const.op_LTE), (uu____13326)))
in (

let uu____13352 = (

let uu____13367 = (

let uu____13380 = (

let uu____13389 = (

let uu____13390 = (

let uu____13391 = (

let uu____13396 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13397 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13396), (uu____13397))))
in (FStar_SMTEncoding_Util.mkGT uu____13391))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13390))
in (quant xy uu____13389))
in ((FStar_Parser_Const.op_GT), (uu____13380)))
in (

let uu____13406 = (

let uu____13421 = (

let uu____13434 = (

let uu____13443 = (

let uu____13444 = (

let uu____13445 = (

let uu____13450 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13451 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13450), (uu____13451))))
in (FStar_SMTEncoding_Util.mkGTE uu____13445))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13444))
in (quant xy uu____13443))
in ((FStar_Parser_Const.op_GTE), (uu____13434)))
in (

let uu____13460 = (

let uu____13475 = (

let uu____13488 = (

let uu____13497 = (

let uu____13498 = (

let uu____13499 = (

let uu____13504 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13505 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13504), (uu____13505))))
in (FStar_SMTEncoding_Util.mkSub uu____13499))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13498))
in (quant xy uu____13497))
in ((FStar_Parser_Const.op_Subtraction), (uu____13488)))
in (

let uu____13514 = (

let uu____13529 = (

let uu____13542 = (

let uu____13551 = (

let uu____13552 = (

let uu____13553 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____13553))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13552))
in (quant qx uu____13551))
in ((FStar_Parser_Const.op_Minus), (uu____13542)))
in (

let uu____13562 = (

let uu____13577 = (

let uu____13590 = (

let uu____13599 = (

let uu____13600 = (

let uu____13601 = (

let uu____13606 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13607 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13606), (uu____13607))))
in (FStar_SMTEncoding_Util.mkAdd uu____13601))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13600))
in (quant xy uu____13599))
in ((FStar_Parser_Const.op_Addition), (uu____13590)))
in (

let uu____13616 = (

let uu____13631 = (

let uu____13644 = (

let uu____13653 = (

let uu____13654 = (

let uu____13655 = (

let uu____13660 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13661 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13660), (uu____13661))))
in (FStar_SMTEncoding_Util.mkMul uu____13655))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13654))
in (quant xy uu____13653))
in ((FStar_Parser_Const.op_Multiply), (uu____13644)))
in (

let uu____13670 = (

let uu____13685 = (

let uu____13698 = (

let uu____13707 = (

let uu____13708 = (

let uu____13709 = (

let uu____13714 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13715 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13714), (uu____13715))))
in (FStar_SMTEncoding_Util.mkDiv uu____13709))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13708))
in (quant xy uu____13707))
in ((FStar_Parser_Const.op_Division), (uu____13698)))
in (

let uu____13724 = (

let uu____13739 = (

let uu____13752 = (

let uu____13761 = (

let uu____13762 = (

let uu____13763 = (

let uu____13768 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13769 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13768), (uu____13769))))
in (FStar_SMTEncoding_Util.mkMod uu____13763))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13762))
in (quant xy uu____13761))
in ((FStar_Parser_Const.op_Modulus), (uu____13752)))
in (

let uu____13778 = (

let uu____13793 = (

let uu____13806 = (

let uu____13815 = (

let uu____13816 = (

let uu____13817 = (

let uu____13822 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____13823 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____13822), (uu____13823))))
in (FStar_SMTEncoding_Util.mkAnd uu____13817))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13816))
in (quant xy uu____13815))
in ((FStar_Parser_Const.op_And), (uu____13806)))
in (

let uu____13832 = (

let uu____13847 = (

let uu____13860 = (

let uu____13869 = (

let uu____13870 = (

let uu____13871 = (

let uu____13876 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____13877 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____13876), (uu____13877))))
in (FStar_SMTEncoding_Util.mkOr uu____13871))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13870))
in (quant xy uu____13869))
in ((FStar_Parser_Const.op_Or), (uu____13860)))
in (

let uu____13886 = (

let uu____13901 = (

let uu____13914 = (

let uu____13923 = (

let uu____13924 = (

let uu____13925 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____13925))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13924))
in (quant qx uu____13923))
in ((FStar_Parser_Const.op_Negation), (uu____13914)))
in (uu____13901)::[])
in (uu____13847)::uu____13886))
in (uu____13793)::uu____13832))
in (uu____13739)::uu____13778))
in (uu____13685)::uu____13724))
in (uu____13631)::uu____13670))
in (uu____13577)::uu____13616))
in (uu____13529)::uu____13562))
in (uu____13475)::uu____13514))
in (uu____13421)::uu____13460))
in (uu____13367)::uu____13406))
in (uu____13313)::uu____13352))
in (uu____13259)::uu____13298))
in (uu____13211)::uu____13244))
in (uu____13164)::uu____13196))
in (

let mk1 = (fun l v1 -> (

let uu____14139 = (

let uu____14148 = (FStar_All.pipe_right prims1 (FStar_List.find (fun uu____14206 -> (match (uu____14206) with
| (l', uu____14220) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____14148 (FStar_Option.map (fun uu____14280 -> (match (uu____14280) with
| (uu____14299, b) -> begin
(b v1)
end)))))
in (FStar_All.pipe_right uu____14139 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims1 (FStar_Util.for_some (fun uu____14370 -> (match (uu____14370) with
| (l', uu____14384) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk1; is = is})))))))
end))
end))
end))


let pretype_axiom : env_t  ->  FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun env tapp vars -> (

let uu____14425 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____14425) with
| (xxsym, xx) -> begin
(

let uu____14432 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____14432) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let module_name = env.current_module_name
in (

let uu____14442 = (

let uu____14449 = (

let uu____14450 = (

let uu____14461 = (

let uu____14462 = (

let uu____14467 = (

let uu____14468 = (

let uu____14473 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____14473)))
in (FStar_SMTEncoding_Util.mkEq uu____14468))
in ((xx_has_type), (uu____14467)))
in (FStar_SMTEncoding_Util.mkImp uu____14462))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____14461)))
in (FStar_SMTEncoding_Util.mkForall uu____14450))
in (

let uu____14498 = (

let uu____14499 = (

let uu____14500 = (

let uu____14501 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "_pretyping_" uu____14501))
in (Prims.strcat module_name uu____14500))
in (varops.mk_unique uu____14499))
in ((uu____14449), (FStar_Pervasives_Native.Some ("pretyping")), (uu____14498))))
in (FStar_SMTEncoding_Util.mkAssume uu____14442)))))
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
in (

let uu____14541 = (

let uu____14542 = (

let uu____14549 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____14549), (FStar_Pervasives_Native.Some ("unit typing")), ("unit_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____14542))
in (

let uu____14552 = (

let uu____14555 = (

let uu____14556 = (

let uu____14563 = (

let uu____14564 = (

let uu____14575 = (

let uu____14576 = (

let uu____14581 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____14581)))
in (FStar_SMTEncoding_Util.mkImp uu____14576))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____14575)))
in (mkForall_fuel uu____14564))
in ((uu____14563), (FStar_Pervasives_Native.Some ("unit inversion")), ("unit_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____14556))
in (uu____14555)::[])
in (uu____14541)::uu____14552))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____14623 = (

let uu____14624 = (

let uu____14631 = (

let uu____14632 = (

let uu____14643 = (

let uu____14648 = (

let uu____14651 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____14651)::[])
in (uu____14648)::[])
in (

let uu____14656 = (

let uu____14657 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____14657 tt))
in ((uu____14643), ((bb)::[]), (uu____14656))))
in (FStar_SMTEncoding_Util.mkForall uu____14632))
in ((uu____14631), (FStar_Pervasives_Native.Some ("bool typing")), ("bool_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____14624))
in (

let uu____14678 = (

let uu____14681 = (

let uu____14682 = (

let uu____14689 = (

let uu____14690 = (

let uu____14701 = (

let uu____14702 = (

let uu____14707 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxBoolFun) x)
in ((typing_pred), (uu____14707)))
in (FStar_SMTEncoding_Util.mkImp uu____14702))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____14701)))
in (mkForall_fuel uu____14690))
in ((uu____14689), (FStar_Pervasives_Native.Some ("bool inversion")), ("bool_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____14682))
in (uu____14681)::[])
in (uu____14623)::uu____14678))))))
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

let precedes = (

let uu____14757 = (

let uu____14758 = (

let uu____14765 = (

let uu____14768 = (

let uu____14771 = (

let uu____14774 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____14775 = (

let uu____14778 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____14778)::[])
in (uu____14774)::uu____14775))
in (tt)::uu____14771)
in (tt)::uu____14768)
in (("Prims.Precedes"), (uu____14765)))
in (FStar_SMTEncoding_Util.mkApp uu____14758))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14757))
in (

let precedes_y_x = (

let uu____14782 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14782))
in (

let uu____14785 = (

let uu____14786 = (

let uu____14793 = (

let uu____14794 = (

let uu____14805 = (

let uu____14810 = (

let uu____14813 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____14813)::[])
in (uu____14810)::[])
in (

let uu____14818 = (

let uu____14819 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____14819 tt))
in ((uu____14805), ((bb)::[]), (uu____14818))))
in (FStar_SMTEncoding_Util.mkForall uu____14794))
in ((uu____14793), (FStar_Pervasives_Native.Some ("int typing")), ("int_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____14786))
in (

let uu____14840 = (

let uu____14843 = (

let uu____14844 = (

let uu____14851 = (

let uu____14852 = (

let uu____14863 = (

let uu____14864 = (

let uu____14869 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxIntFun) x)
in ((typing_pred), (uu____14869)))
in (FStar_SMTEncoding_Util.mkImp uu____14864))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____14863)))
in (mkForall_fuel uu____14852))
in ((uu____14851), (FStar_Pervasives_Native.Some ("int inversion")), ("int_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____14844))
in (

let uu____14894 = (

let uu____14897 = (

let uu____14898 = (

let uu____14905 = (

let uu____14906 = (

let uu____14917 = (

let uu____14918 = (

let uu____14923 = (

let uu____14924 = (

let uu____14927 = (

let uu____14930 = (

let uu____14933 = (

let uu____14934 = (

let uu____14939 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14940 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____14939), (uu____14940))))
in (FStar_SMTEncoding_Util.mkGT uu____14934))
in (

let uu____14941 = (

let uu____14944 = (

let uu____14945 = (

let uu____14950 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____14951 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____14950), (uu____14951))))
in (FStar_SMTEncoding_Util.mkGTE uu____14945))
in (

let uu____14952 = (

let uu____14955 = (

let uu____14956 = (

let uu____14961 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____14962 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____14961), (uu____14962))))
in (FStar_SMTEncoding_Util.mkLT uu____14956))
in (uu____14955)::[])
in (uu____14944)::uu____14952))
in (uu____14933)::uu____14941))
in (typing_pred_y)::uu____14930)
in (typing_pred)::uu____14927)
in (FStar_SMTEncoding_Util.mk_and_l uu____14924))
in ((uu____14923), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____14918))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____14917)))
in (mkForall_fuel uu____14906))
in ((uu____14905), (FStar_Pervasives_Native.Some ("well-founded ordering on nat (alt)")), ("well-founded-ordering-on-nat")))
in (FStar_SMTEncoding_Util.mkAssume uu____14898))
in (uu____14897)::[])
in (uu____14843)::uu____14894))
in (uu____14785)::uu____14840)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____15008 = (

let uu____15009 = (

let uu____15016 = (

let uu____15017 = (

let uu____15028 = (

let uu____15033 = (

let uu____15036 = (FStar_SMTEncoding_Term.boxString b)
in (uu____15036)::[])
in (uu____15033)::[])
in (

let uu____15041 = (

let uu____15042 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____15042 tt))
in ((uu____15028), ((bb)::[]), (uu____15041))))
in (FStar_SMTEncoding_Util.mkForall uu____15017))
in ((uu____15016), (FStar_Pervasives_Native.Some ("string typing")), ("string_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15009))
in (

let uu____15063 = (

let uu____15066 = (

let uu____15067 = (

let uu____15074 = (

let uu____15075 = (

let uu____15086 = (

let uu____15087 = (

let uu____15092 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxStringFun) x)
in ((typing_pred), (uu____15092)))
in (FStar_SMTEncoding_Util.mkImp uu____15087))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15086)))
in (mkForall_fuel uu____15075))
in ((uu____15074), (FStar_Pervasives_Native.Some ("string inversion")), ("string_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15067))
in (uu____15066)::[])
in (uu____15008)::uu____15063))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in ((FStar_SMTEncoding_Util.mkAssume ((valid), (FStar_Pervasives_Native.Some ("True interpretation")), ("true_interp"))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____15145 = (

let uu____15146 = (

let uu____15153 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____15153), (FStar_Pervasives_Native.Some ("False interpretation")), ("false_interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15146))
in (uu____15145)::[])))
in (

let mk_and_interp = (fun env conj uu____15165 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let l_and_a_b = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_and_a_b)::[])))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____15190 = (

let uu____15191 = (

let uu____15198 = (

let uu____15199 = (

let uu____15210 = (

let uu____15211 = (

let uu____15216 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____15216), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15211))
in ((((l_and_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15210)))
in (FStar_SMTEncoding_Util.mkForall uu____15199))
in ((uu____15198), (FStar_Pervasives_Native.Some ("/\\ interpretation")), ("l_and-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15191))
in (uu____15190)::[]))))))))))
in (

let mk_or_interp = (fun env disj uu____15254 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let l_or_a_b = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_or_a_b)::[])))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____15279 = (

let uu____15280 = (

let uu____15287 = (

let uu____15288 = (

let uu____15299 = (

let uu____15300 = (

let uu____15305 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____15305), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15300))
in ((((l_or_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15299)))
in (FStar_SMTEncoding_Util.mkForall uu____15288))
in ((uu____15287), (FStar_Pervasives_Native.Some ("\\/ interpretation")), ("l_or-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15280))
in (uu____15279)::[]))))))))))
in (

let mk_eq2_interp = (fun env eq2 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx1 = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy1 = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let x1 = (FStar_SMTEncoding_Util.mkFreeV xx1)
in (

let y1 = (FStar_SMTEncoding_Util.mkFreeV yy1)
in (

let eq2_x_y = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x1)::(y1)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((eq2_x_y)::[])))
in (

let uu____15368 = (

let uu____15369 = (

let uu____15376 = (

let uu____15377 = (

let uu____15388 = (

let uu____15389 = (

let uu____15394 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____15394), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15389))
in ((((eq2_x_y)::[])::[]), ((aa)::(xx1)::(yy1)::[]), (uu____15388)))
in (FStar_SMTEncoding_Util.mkForall uu____15377))
in ((uu____15376), (FStar_Pervasives_Native.Some ("Eq2 interpretation")), ("eq2-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15369))
in (uu____15368)::[]))))))))))
in (

let mk_eq3_interp = (fun env eq3 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx1 = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy1 = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x1 = (FStar_SMTEncoding_Util.mkFreeV xx1)
in (

let y1 = (FStar_SMTEncoding_Util.mkFreeV yy1)
in (

let eq3_x_y = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x1)::(y1)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((eq3_x_y)::[])))
in (

let uu____15467 = (

let uu____15468 = (

let uu____15475 = (

let uu____15476 = (

let uu____15487 = (

let uu____15488 = (

let uu____15493 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____15493), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15488))
in ((((eq3_x_y)::[])::[]), ((aa)::(bb)::(xx1)::(yy1)::[]), (uu____15487)))
in (FStar_SMTEncoding_Util.mkForall uu____15476))
in ((uu____15475), (FStar_Pervasives_Native.Some ("Eq3 interpretation")), ("eq3-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15468))
in (uu____15467)::[]))))))))))))
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

let l_imp_a_b = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_imp_a_b)::[])))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____15564 = (

let uu____15565 = (

let uu____15572 = (

let uu____15573 = (

let uu____15584 = (

let uu____15585 = (

let uu____15590 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____15590), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15585))
in ((((l_imp_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15584)))
in (FStar_SMTEncoding_Util.mkForall uu____15573))
in ((uu____15572), (FStar_Pervasives_Native.Some ("==> interpretation")), ("l_imp-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15565))
in (uu____15564)::[]))))))))))
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

let l_iff_a_b = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_iff_a_b)::[])))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____15653 = (

let uu____15654 = (

let uu____15661 = (

let uu____15662 = (

let uu____15673 = (

let uu____15674 = (

let uu____15679 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____15679), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15674))
in ((((l_iff_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15673)))
in (FStar_SMTEncoding_Util.mkForall uu____15662))
in ((uu____15661), (FStar_Pervasives_Native.Some ("<==> interpretation")), ("l_iff-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15654))
in (uu____15653)::[]))))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let l_not_a = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_not_a)::[])))
in (

let not_valid_a = (

let uu____15731 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15731))
in (

let uu____15734 = (

let uu____15735 = (

let uu____15742 = (

let uu____15743 = (

let uu____15754 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((l_not_a)::[])::[]), ((aa)::[]), (uu____15754)))
in (FStar_SMTEncoding_Util.mkForall uu____15743))
in ((uu____15742), (FStar_Pervasives_Native.Some ("not interpretation")), ("l_not-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15735))
in (uu____15734)::[])))))))
in (

let mk_forall_interp = (fun env for_all1 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx1 = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x1 = (FStar_SMTEncoding_Util.mkFreeV xx1)
in (

let l_forall_a_b = (FStar_SMTEncoding_Util.mkApp ((for_all1), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_forall_a_b)::[])))
in (

let valid_b_x = (

let uu____15814 = (

let uu____15821 = (

let uu____15824 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____15824)::[])
in (("Valid"), (uu____15821)))
in (FStar_SMTEncoding_Util.mkApp uu____15814))
in (

let uu____15827 = (

let uu____15828 = (

let uu____15835 = (

let uu____15836 = (

let uu____15847 = (

let uu____15848 = (

let uu____15853 = (

let uu____15854 = (

let uu____15865 = (

let uu____15870 = (

let uu____15873 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____15873)::[])
in (uu____15870)::[])
in (

let uu____15878 = (

let uu____15879 = (

let uu____15884 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____15884), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____15879))
in ((uu____15865), ((xx1)::[]), (uu____15878))))
in (FStar_SMTEncoding_Util.mkForall uu____15854))
in ((uu____15853), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15848))
in ((((l_forall_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15847)))
in (FStar_SMTEncoding_Util.mkForall uu____15836))
in ((uu____15835), (FStar_Pervasives_Native.Some ("forall interpretation")), ("forall-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15828))
in (uu____15827)::[])))))))))))
in (

let mk_exists_interp = (fun env for_some1 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx1 = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x1 = (FStar_SMTEncoding_Util.mkFreeV xx1)
in (

let l_exists_a_b = (FStar_SMTEncoding_Util.mkApp ((for_some1), ((a)::(b)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((l_exists_a_b)::[])))
in (

let valid_b_x = (

let uu____15966 = (

let uu____15973 = (

let uu____15976 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____15976)::[])
in (("Valid"), (uu____15973)))
in (FStar_SMTEncoding_Util.mkApp uu____15966))
in (

let uu____15979 = (

let uu____15980 = (

let uu____15987 = (

let uu____15988 = (

let uu____15999 = (

let uu____16000 = (

let uu____16005 = (

let uu____16006 = (

let uu____16017 = (

let uu____16022 = (

let uu____16025 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____16025)::[])
in (uu____16022)::[])
in (

let uu____16030 = (

let uu____16031 = (

let uu____16036 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____16036), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____16031))
in ((uu____16017), ((xx1)::[]), (uu____16030))))
in (FStar_SMTEncoding_Util.mkExists uu____16006))
in ((uu____16005), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16000))
in ((((l_exists_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15999)))
in (FStar_SMTEncoding_Util.mkForall uu____15988))
in ((uu____15987), (FStar_Pervasives_Native.Some ("exists interpretation")), ("exists-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15980))
in (uu____15979)::[])))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____16096 = (

let uu____16097 = (

let uu____16104 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (

let uu____16105 = (varops.mk_unique "typing_range_const")
in ((uu____16104), (FStar_Pervasives_Native.Some ("Range_const typing")), (uu____16105))))
in (FStar_SMTEncoding_Util.mkAssume uu____16097))
in (uu____16096)::[])))
in (

let mk_inversion_axiom = (fun env inversion tt -> (

let tt1 = (("t"), (FStar_SMTEncoding_Term.Term_sort))
in (

let t = (FStar_SMTEncoding_Util.mkFreeV tt1)
in (

let xx1 = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x1 = (FStar_SMTEncoding_Util.mkFreeV xx1)
in (

let inversion_t = (FStar_SMTEncoding_Util.mkApp ((inversion), ((t)::[])))
in (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((inversion_t)::[])))
in (

let body = (

let hastypeZ = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 t)
in (

let hastypeS = (

let uu____16139 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1"))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16139 x1 t))
in (

let uu____16140 = (

let uu____16151 = (FStar_SMTEncoding_Util.mkImp ((hastypeZ), (hastypeS)))
in ((((hastypeZ)::[])::[]), ((xx1)::[]), (uu____16151)))
in (FStar_SMTEncoding_Util.mkForall uu____16140))))
in (

let uu____16174 = (

let uu____16175 = (

let uu____16182 = (

let uu____16183 = (

let uu____16194 = (FStar_SMTEncoding_Util.mkImp ((valid), (body)))
in ((((inversion_t)::[])::[]), ((tt1)::[]), (uu____16194)))
in (FStar_SMTEncoding_Util.mkForall uu____16183))
in ((uu____16182), (FStar_Pervasives_Native.Some ("inversion interpretation")), ("inversion-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16175))
in (uu____16174)::[])))))))))
in (

let prims1 = (((FStar_Parser_Const.unit_lid), (mk_unit)))::(((FStar_Parser_Const.bool_lid), (mk_bool)))::(((FStar_Parser_Const.int_lid), (mk_int)))::(((FStar_Parser_Const.string_lid), (mk_str)))::(((FStar_Parser_Const.true_lid), (mk_true_interp)))::(((FStar_Parser_Const.false_lid), (mk_false_interp)))::(((FStar_Parser_Const.and_lid), (mk_and_interp)))::(((FStar_Parser_Const.or_lid), (mk_or_interp)))::(((FStar_Parser_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Parser_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Parser_Const.imp_lid), (mk_imp_interp)))::(((FStar_Parser_Const.iff_lid), (mk_iff_interp)))::(((FStar_Parser_Const.not_lid), (mk_not_interp)))::(((FStar_Parser_Const.forall_lid), (mk_forall_interp)))::(((FStar_Parser_Const.exists_lid), (mk_exists_interp)))::(((FStar_Parser_Const.range_lid), (mk_range_interp)))::(((FStar_Parser_Const.inversion_lid), (mk_inversion_axiom)))::[]
in (fun env t s tt -> (

let uu____16518 = (FStar_Util.find_opt (fun uu____16544 -> (match (uu____16544) with
| (l, uu____16556) -> begin
(FStar_Ident.lid_equals l t)
end)) prims1)
in (match (uu____16518) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____16581, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____16620 = (encode_function_type_as_formula t env)
in (match (uu____16620) with
| (form, decls) -> begin
(FStar_List.append decls (((FStar_SMTEncoding_Util.mkAssume ((form), (FStar_Pervasives_Native.Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))


let encode_free_var : Prims.bool  ->  env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun uninterpreted env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____16666 = (((

let uu____16669 = ((FStar_Syntax_Util.is_pure_or_ghost_function t_norm) || (FStar_TypeChecker_Env.is_reifiable_function env.tcenv t_norm))
in (FStar_All.pipe_left Prims.op_Negation uu____16669)) || (FStar_Syntax_Util.is_lemma t_norm)) || uninterpreted)
in (match (uu____16666) with
| true -> begin
(

let uu____16676 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____16676) with
| (vname, vtok, env1) -> begin
(

let arg_sorts = (

let uu____16695 = (

let uu____16696 = (FStar_Syntax_Subst.compress t_norm)
in uu____16696.FStar_Syntax_Syntax.n)
in (match (uu____16695) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____16702) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____16732 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____16737 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env1)))))
end))
end
| uu____16750 -> begin
(

let uu____16751 = (prims.is lid)
in (match (uu____16751) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____16759 = (prims.mk lid vname)
in (match (uu____16759) with
| (tok, definition) -> begin
(

let env1 = (push_free_var env lid vname (FStar_Pervasives_Native.Some (tok)))
in ((definition), (env1)))
end)))
end
| uu____16781 -> begin
(

let encode_non_total_function_typ = (Prims.op_disEquality lid.FStar_Ident.nsstr "Prims")
in (

let uu____16783 = (

let uu____16794 = (curried_arrow_formals_comp t_norm)
in (match (uu____16794) with
| (args, comp) -> begin
(

let comp1 = (

let uu____16812 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv comp)
in (match (uu____16812) with
| true -> begin
(

let uu____16813 = (FStar_TypeChecker_Env.reify_comp (

let uu___165_16816 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___165_16816.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___165_16816.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___165_16816.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___165_16816.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___165_16816.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___165_16816.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___165_16816.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___165_16816.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___165_16816.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___165_16816.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___165_16816.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___165_16816.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___165_16816.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___165_16816.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___165_16816.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___165_16816.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___165_16816.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___165_16816.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___165_16816.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___165_16816.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___165_16816.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___165_16816.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___165_16816.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___165_16816.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___165_16816.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___165_16816.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___165_16816.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___165_16816.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___165_16816.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.dsenv = uu___165_16816.FStar_TypeChecker_Env.dsenv}) comp FStar_Syntax_Syntax.U_unknown)
in (FStar_Syntax_Syntax.mk_Total uu____16813))
end
| uu____16817 -> begin
comp
end))
in (match (encode_non_total_function_typ) with
| true -> begin
(

let uu____16828 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp1)
in ((args), (uu____16828)))
end
| uu____16841 -> begin
((args), (((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp1)))))
end))
end))
in (match (uu____16783) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____16873 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____16873) with
| (vname, vtok, env1) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____16894 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___137_16936 -> (match (uu___137_16936) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____16940 = (FStar_Util.prefix vars)
in (match (uu____16940) with
| (uu____16961, (xxsym, uu____16963)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____16981 = (

let uu____16982 = (

let uu____16989 = (

let uu____16990 = (

let uu____17001 = (

let uu____17002 = (

let uu____17007 = (

let uu____17008 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____17008))
in ((vapp), (uu____17007)))
in (FStar_SMTEncoding_Util.mkEq uu____17002))
in ((((vapp)::[])::[]), (vars), (uu____17001)))
in (FStar_SMTEncoding_Util.mkForall uu____16990))
in ((uu____16989), (FStar_Pervasives_Native.Some ("Discriminator equation")), ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))
in (FStar_SMTEncoding_Util.mkAssume uu____16982))
in (uu____16981)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____17027 = (FStar_Util.prefix vars)
in (match (uu____17027) with
| (uu____17048, (xxsym, uu____17050)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f1 = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f1)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____17073 = (

let uu____17074 = (

let uu____17081 = (

let uu____17082 = (

let uu____17093 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____17093)))
in (FStar_SMTEncoding_Util.mkForall uu____17082))
in ((uu____17081), (FStar_Pervasives_Native.Some ("Projector equation")), ((Prims.strcat "proj_equation_" tp_name))))
in (FStar_SMTEncoding_Util.mkAssume uu____17074))
in (uu____17073)::[])))))
end))
end
| uu____17110 -> begin
[]
end)))))
in (

let uu____17111 = (encode_binders FStar_Pervasives_Native.None formals env1)
in (match (uu____17111) with
| (vars, guards, env', decls1, uu____17138) -> begin
(

let uu____17151 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17160 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____17160), (decls1)))
end
| FStar_Pervasives_Native.Some (p) -> begin
(

let uu____17162 = (encode_formula p env')
in (match (uu____17162) with
| (g, ds) -> begin
(

let uu____17173 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____17173), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____17151) with
| (guard, decls11) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____17186 = (

let uu____17193 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____17193)))
in (FStar_SMTEncoding_Util.mkApp uu____17186))
in (

let uu____17202 = (

let vname_decl = (

let uu____17210 = (

let uu____17221 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____17231 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____17221), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____17210))
in (

let uu____17240 = (

let env2 = (

let uu___166_17246 = env1
in {bindings = uu___166_17246.bindings; depth = uu___166_17246.depth; tcenv = uu___166_17246.tcenv; warn = uu___166_17246.warn; cache = uu___166_17246.cache; nolabels = uu___166_17246.nolabels; use_zfuel_name = uu___166_17246.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = uu___166_17246.current_module_name})
in (

let uu____17247 = (

let uu____17248 = (head_normal env2 tt)
in (not (uu____17248)))
in (match (uu____17247) with
| true -> begin
(encode_term_pred FStar_Pervasives_Native.None tt env2 vtok_tm)
end
| uu____17253 -> begin
(encode_term_pred FStar_Pervasives_Native.None t_norm env2 vtok_tm)
end)))
in (match (uu____17240) with
| (tok_typing, decls2) -> begin
(

let tok_typing1 = (match (formals) with
| (uu____17263)::uu____17264 -> begin
(

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (mk_Apply vtok_tm ((ff)::[]))
in (

let vtok_app_r = (mk_Apply f ((((vtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let guarded_tok_typing = (

let uu____17304 = (

let uu____17315 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____17315)))
in (FStar_SMTEncoding_Util.mkForall uu____17304))
in (FStar_SMTEncoding_Util.mkAssume ((guarded_tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname)))))))))
end
| uu____17342 -> begin
(FStar_SMTEncoding_Util.mkAssume ((tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname))))
end)
in (

let uu____17345 = (match (formals) with
| [] -> begin
(

let uu____17362 = (

let uu____17363 = (

let uu____17366 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_43 -> FStar_Pervasives_Native.Some (_0_43)) uu____17366))
in (push_free_var env1 lid vname uu____17363))
in (((FStar_List.append decls2 ((tok_typing1)::[]))), (uu____17362)))
end
| uu____17371 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let vtok_fresh = (

let uu____17378 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) uu____17378))
in (

let name_tok_corr = (

let uu____17380 = (

let uu____17387 = (

let uu____17388 = (

let uu____17399 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____17399)))
in (FStar_SMTEncoding_Util.mkForall uu____17388))
in ((uu____17387), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____17380))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing1)::[]))), (env1)))))
end)
in (match (uu____17345) with
| (tok_decl, env2) -> begin
(((vname_decl)::tok_decl), (env2))
end)))
end)))
in (match (uu____17202) with
| (decls2, env2) -> begin
(

let uu____17442 = (

let res_t1 = (FStar_Syntax_Subst.compress res_t)
in (

let uu____17450 = (encode_term res_t1 env')
in (match (uu____17450) with
| (encoded_res_t, decls) -> begin
(

let uu____17463 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____17463), (decls)))
end)))
in (match (uu____17442) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____17474 = (

let uu____17481 = (

let uu____17482 = (

let uu____17493 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____17493)))
in (FStar_SMTEncoding_Util.mkForall uu____17482))
in ((uu____17481), (FStar_Pervasives_Native.Some ("free var typing")), ((Prims.strcat "typing_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____17474))
in (

let freshness = (

let uu____17509 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____17509) with
| true -> begin
(

let uu____17514 = (

let uu____17515 = (

let uu____17526 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in (

let uu____17537 = (varops.next_id ())
in ((vname), (uu____17526), (FStar_SMTEncoding_Term.Term_sort), (uu____17537))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____17515))
in (

let uu____17540 = (

let uu____17543 = (pretype_axiom env2 vapp vars)
in (uu____17543)::[])
in (uu____17514)::uu____17540))
end
| uu____17544 -> begin
[]
end))
in (

let g = (

let uu____17548 = (

let uu____17551 = (

let uu____17554 = (

let uu____17557 = (

let uu____17560 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____17560)
in (FStar_List.append freshness uu____17557))
in (FStar_List.append decls3 uu____17554))
in (FStar_List.append decls2 uu____17551))
in (FStar_List.append decls11 uu____17548))
in ((g), (env2)))))
end))
end))))
end))
end))))
end))
end)))
end))
end))))


let declare_top_level_let : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (

let uu____17595 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17595) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17632 = (encode_free_var false env x t t_norm [])
in (match (uu____17632) with
| (decls, env1) -> begin
(

let uu____17659 = (lookup_lid env1 x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17659) with
| (n1, x', uu____17686) -> begin
((((n1), (x'))), (decls), (env1))
end))
end))
end
| FStar_Pervasives_Native.Some (n1, x1, uu____17707) -> begin
((((n1), (x1))), ([]), (env))
end)))


let encode_top_level_val : Prims.bool  ->  env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun uninterpreted env lid t quals -> (

let tt = (norm env t)
in (

let uu____17767 = (encode_free_var uninterpreted env lid t tt quals)
in (match (uu____17767) with
| (decls, env1) -> begin
(

let uu____17786 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____17786) with
| true -> begin
(

let uu____17793 = (

let uu____17796 = (encode_smt_lemma env1 lid tt)
in (FStar_List.append decls uu____17796))
in ((uu____17793), (env1)))
end
| uu____17801 -> begin
((decls), (env1))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____17851 lb -> (match (uu____17851) with
| (decls, env1) -> begin
(

let uu____17871 = (

let uu____17878 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val false env1 uu____17878 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____17871) with
| (decls', env2) -> begin
(((FStar_List.append decls decls')), (env2))
end))
end)) (([]), (env)))))


let is_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let fstar_tactics_tactic_lid = (FStar_Parser_Const.p2l (("FStar")::("Tactics")::("tactic")::[]))
in (

let uu____17900 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____17900) with
| (hd1, args) -> begin
(

let uu____17937 = (

let uu____17938 = (FStar_Syntax_Util.un_uinst hd1)
in uu____17938.FStar_Syntax_Syntax.n)
in (match (uu____17937) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____17942, c) -> begin
(

let effect_name = (FStar_Syntax_Util.comp_effect_name c)
in (FStar_Util.starts_with "FStar.Tactics" effect_name.FStar_Ident.str))
end
| uu____17961 -> begin
false
end))
end))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____17986 quals -> (match (uu____17986) with
| (is_rec, bindings) -> begin
(

let eta_expand1 = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____18062 = (FStar_Util.first_N nbinders formals)
in (match (uu____18062) with
| (formals1, extra_formals) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____18143 uu____18144 -> (match (((uu____18143), (uu____18144))) with
| ((formal, uu____18162), (binder, uu____18164)) -> begin
(

let uu____18173 = (

let uu____18180 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____18180)))
in FStar_Syntax_Syntax.NT (uu____18173))
end)) formals1 binders)
in (

let extra_formals1 = (

let uu____18188 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____18219 -> (match (uu____18219) with
| (x, i) -> begin
(

let uu____18230 = (

let uu___167_18231 = x
in (

let uu____18232 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___167_18231.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___167_18231.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____18232}))
in ((uu____18230), (i)))
end))))
in (FStar_All.pipe_right uu____18188 FStar_Syntax_Util.name_binders))
in (

let body1 = (

let uu____18250 = (

let uu____18251 = (FStar_Syntax_Subst.compress body)
in (

let uu____18252 = (

let uu____18253 = (FStar_Syntax_Util.args_of_binders extra_formals1)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____18253))
in (FStar_Syntax_Syntax.extend_app_n uu____18251 uu____18252)))
in (uu____18250 FStar_Pervasives_Native.None body.FStar_Syntax_Syntax.pos))
in (((FStar_List.append binders extra_formals1)), (body1)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let get_result_type = (fun c -> (

let uu____18314 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c)
in (match (uu____18314) with
| true -> begin
(FStar_TypeChecker_Env.reify_comp (

let uu___168_18317 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___168_18317.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___168_18317.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___168_18317.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___168_18317.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___168_18317.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___168_18317.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___168_18317.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___168_18317.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___168_18317.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___168_18317.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___168_18317.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___168_18317.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___168_18317.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___168_18317.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___168_18317.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___168_18317.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___168_18317.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___168_18317.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___168_18317.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___168_18317.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___168_18317.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___168_18317.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___168_18317.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___168_18317.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___168_18317.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___168_18317.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___168_18317.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___168_18317.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___168_18317.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.dsenv = uu___168_18317.FStar_TypeChecker_Env.dsenv}) c FStar_Syntax_Syntax.U_unknown)
end
| uu____18318 -> begin
(FStar_Syntax_Util.comp_result c)
end)))
in (

let rec aux = (fun norm1 t_norm1 -> (

let uu____18350 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____18350) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____18414)::uu____18415 -> begin
(

let uu____18430 = (

let uu____18431 = (

let uu____18434 = (FStar_Syntax_Subst.compress t_norm1)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____18434))
in uu____18431.FStar_Syntax_Syntax.n)
in (match (uu____18430) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____18477 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____18477) with
| (formals1, c1) -> begin
(

let nformals = (FStar_List.length formals1)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (get_result_type c1)
in (

let uu____18519 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c1))
in (match (uu____18519) with
| true -> begin
(

let uu____18554 = (FStar_Util.first_N nformals binders)
in (match (uu____18554) with
| (bs0, rest) -> begin
(

let c2 = (

let subst1 = (FStar_List.map2 (fun uu____18648 uu____18649 -> (match (((uu____18648), (uu____18649))) with
| ((x, uu____18667), (b, uu____18669)) -> begin
(

let uu____18678 = (

let uu____18685 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____18685)))
in FStar_Syntax_Syntax.NT (uu____18678))
end)) formals1 bs0)
in (FStar_Syntax_Subst.subst_comp subst1 c1))
in (

let body1 = (FStar_Syntax_Util.abs rest body lopt)
in (

let uu____18687 = (

let uu____18708 = (get_result_type c2)
in ((bs0), (body1), (bs0), (uu____18708)))
in ((uu____18687), (false)))))
end))
end
| uu____18741 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____18776 = (eta_expand1 binders formals1 body tres)
in (match (uu____18776) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end))
end
| uu____18855 -> begin
((((binders), (body), (formals1), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____18865) -> begin
(

let uu____18870 = (

let uu____18891 = (aux norm1 x.FStar_Syntax_Syntax.sort)
in (FStar_Pervasives_Native.fst uu____18891))
in ((uu____18870), (true)))
end
| uu____18956 when (not (norm1)) -> begin
(

let t_norm2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm1)
in (aux true t_norm2))
end
| uu____18958 -> begin
(

let uu____18959 = (

let uu____18960 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____18961 = (FStar_Syntax_Print.term_to_string t_norm1)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____18960 uu____18961)))
in (failwith uu____18959))
end))
end
| uu____18986 -> begin
(

let uu____18987 = (

let uu____18988 = (FStar_Syntax_Subst.compress t_norm1)
in uu____18988.FStar_Syntax_Syntax.n)
in (match (uu____18987) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____19033 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____19033) with
| (formals1, c1) -> begin
(

let tres = (get_result_type c1)
in (

let uu____19065 = (eta_expand1 [] formals1 e tres)
in (match (uu____19065) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end)))
end))
end
| uu____19148 -> begin
(((([]), (e), ([]), (t_norm1))), (false))
end))
end)
end)))
in (aux false t_norm))))
in (FStar_All.try_with (fun uu___170_19197 -> (match (()) with
| () -> begin
(

let uu____19204 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> ((FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))))
in (match (uu____19204) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____19215 -> begin
(

let uu____19216 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____19310 lb -> (match (uu____19310) with
| (toks, typs, decls, env1) -> begin
((

let uu____19405 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____19405) with
| true -> begin
(FStar_Exn.raise Let_rec_unencodeable)
end
| uu____19406 -> begin
()
end));
(

let t_norm = (whnf env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____19408 = (

let uu____19423 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env1 uu____19423 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____19408) with
| (tok, decl, env2) -> begin
(

let uu____19469 = (

let uu____19482 = (

let uu____19493 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((uu____19493), (tok)))
in (uu____19482)::toks)
in ((uu____19469), ((t_norm)::typs), ((decl)::decls), (env2)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____19216) with
| (toks, typs, decls, env1) -> begin
(

let toks1 = (FStar_List.rev toks)
in (

let decls1 = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs1 = (FStar_List.rev typs)
in (

let mk_app1 = (fun curry f ftok vars -> (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____19676 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| FStar_Pervasives_Native.Some (ftok1) -> begin
(mk_Apply ftok1 vars)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____19684 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____19684 vars))
end)
end
| uu____19685 -> begin
(

let uu____19686 = (

let uu____19693 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____19693)))
in (FStar_SMTEncoding_Util.mkApp uu____19686))
end)
end))
in (

let encode_non_rec_lbdef = (fun bindings1 typs2 toks2 env2 -> (match (((bindings1), (typs2), (toks2))) with
| (({FStar_Syntax_Syntax.lbname = uu____19775; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____19777; FStar_Syntax_Syntax.lbeff = uu____19778; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____19841 = (

let uu____19848 = (FStar_TypeChecker_Env.open_universes_in env2.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____19848) with
| (tcenv', uu____19866, e_t) -> begin
(

let uu____19872 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____19883 -> begin
(failwith "Impossible")
end)
in (match (uu____19872) with
| (e1, t_norm1) -> begin
(((

let uu___171_19899 = env2
in {bindings = uu___171_19899.bindings; depth = uu___171_19899.depth; tcenv = tcenv'; warn = uu___171_19899.warn; cache = uu___171_19899.cache; nolabels = uu___171_19899.nolabels; use_zfuel_name = uu___171_19899.use_zfuel_name; encode_non_total_function_typ = uu___171_19899.encode_non_total_function_typ; current_module_name = uu___171_19899.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____19841) with
| (env', e1, t_norm1) -> begin
(

let uu____19909 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____19909) with
| ((binders, body, uu____19930, uu____19931), curry) -> begin
((

let uu____19942 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____19942) with
| true -> begin
(

let uu____19943 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____19944 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____19943 uu____19944)))
end
| uu____19945 -> begin
()
end));
(

let uu____19946 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____19946) with
| (vars, guards, env'1, binder_decls, uu____19973) -> begin
(

let body1 = (

let uu____19987 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____19987) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____19988 -> begin
body
end))
in (

let app = (mk_app1 curry f ftok vars)
in (

let uu____19990 = (

let uu____19999 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____19999) with
| true -> begin
(

let uu____20010 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____20011 = (encode_formula body1 env'1)
in ((uu____20010), (uu____20011))))
end
| uu____20020 -> begin
(

let uu____20021 = (encode_term body1 env'1)
in ((app), (uu____20021)))
end))
in (match (uu____19990) with
| (app1, (body2, decls2)) -> begin
(

let eqn = (

let uu____20044 = (

let uu____20051 = (

let uu____20052 = (

let uu____20063 = (FStar_SMTEncoding_Util.mkEq ((app1), (body2)))
in ((((app1)::[])::[]), (vars), (uu____20063)))
in (FStar_SMTEncoding_Util.mkForall uu____20052))
in (

let uu____20074 = (

let uu____20077 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____20077))
in ((uu____20051), (uu____20074), ((Prims.strcat "equation_" f)))))
in (FStar_SMTEncoding_Util.mkAssume uu____20044))
in (

let uu____20080 = (

let uu____20083 = (

let uu____20086 = (

let uu____20089 = (

let uu____20092 = (primitive_type_axioms env2.tcenv flid f app1)
in (FStar_List.append ((eqn)::[]) uu____20092))
in (FStar_List.append decls2 uu____20089))
in (FStar_List.append binder_decls uu____20086))
in (FStar_List.append decls1 uu____20083))
in ((uu____20080), (env2))))
end))))
end));
)
end))
end)))
end
| uu____20097 -> begin
(failwith "Impossible")
end))
in (

let encode_rec_lbdefs = (fun bindings1 typs2 toks2 env2 -> (

let fuel = (

let uu____20182 = (varops.fresh "fuel")
in ((uu____20182), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env2
in (

let uu____20185 = (FStar_All.pipe_right toks2 (FStar_List.fold_left (fun uu____20273 uu____20274 -> (match (((uu____20273), (uu____20274))) with
| ((gtoks, env3), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (

let uu____20422 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____20422))
in (

let gtok = (

let uu____20424 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____20424))
in (

let env4 = (

let uu____20426 = (

let uu____20429 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_44 -> FStar_Pervasives_Native.Some (_0_44)) uu____20429))
in (push_free_var env3 flid gtok uu____20426))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env4))))))
end)) (([]), (env2))))
in (match (uu____20185) with
| (gtoks, env3) -> begin
(

let gtoks1 = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env01 uu____20585 t_norm uu____20587 -> (match (((uu____20585), (uu____20587))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____20631; FStar_Syntax_Syntax.lbeff = uu____20632; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let uu____20660 = (

let uu____20667 = (FStar_TypeChecker_Env.open_universes_in env3.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____20667) with
| (tcenv', uu____20689, e_t) -> begin
(

let uu____20695 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____20706 -> begin
(failwith "Impossible")
end)
in (match (uu____20695) with
| (e1, t_norm1) -> begin
(((

let uu___172_20722 = env3
in {bindings = uu___172_20722.bindings; depth = uu___172_20722.depth; tcenv = tcenv'; warn = uu___172_20722.warn; cache = uu___172_20722.cache; nolabels = uu___172_20722.nolabels; use_zfuel_name = uu___172_20722.use_zfuel_name; encode_non_total_function_typ = uu___172_20722.encode_non_total_function_typ; current_module_name = uu___172_20722.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____20660) with
| (env', e1, t_norm1) -> begin
((

let uu____20737 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____20737) with
| true -> begin
(

let uu____20738 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____20739 = (FStar_Syntax_Print.term_to_string t_norm1)
in (

let uu____20740 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____20738 uu____20739 uu____20740))))
end
| uu____20741 -> begin
()
end));
(

let uu____20742 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____20742) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____20779 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____20779) with
| true -> begin
(

let uu____20780 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____20781 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____20782 = (FStar_Syntax_Print.binders_to_string ", " formals)
in (

let uu____20783 = (FStar_Syntax_Print.term_to_string tres)
in (FStar_Util.print4 "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n" uu____20780 uu____20781 uu____20782 uu____20783)))))
end
| uu____20784 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____20786 -> begin
()
end);
(

let uu____20787 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____20787) with
| (vars, guards, env'1, binder_decls, uu____20818) -> begin
(

let decl_g = (

let uu____20832 = (

let uu____20843 = (

let uu____20846 = (FStar_List.map FStar_Pervasives_Native.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____20846)
in ((g), (uu____20843), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____20832))
in (

let env02 = (push_zfuel_name env01 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____20871 = (

let uu____20878 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____20878)))
in (FStar_SMTEncoding_Util.mkApp uu____20871))
in (

let gsapp = (

let uu____20888 = (

let uu____20895 = (

let uu____20898 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____20898)::vars_tm)
in ((g), (uu____20895)))
in (FStar_SMTEncoding_Util.mkApp uu____20888))
in (

let gmax = (

let uu____20904 = (

let uu____20911 = (

let uu____20914 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____20914)::vars_tm)
in ((g), (uu____20911)))
in (FStar_SMTEncoding_Util.mkApp uu____20904))
in (

let body1 = (

let uu____20920 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____20920) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____20921 -> begin
body
end))
in (

let uu____20922 = (encode_term body1 env'1)
in (match (uu____20922) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____20940 = (

let uu____20947 = (

let uu____20948 = (

let uu____20963 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____20963)))
in (FStar_SMTEncoding_Util.mkForall' uu____20948))
in (

let uu____20984 = (

let uu____20987 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____20987))
in ((uu____20947), (uu____20984), ((Prims.strcat "equation_with_fuel_" g)))))
in (FStar_SMTEncoding_Util.mkAssume uu____20940))
in (

let eqn_f = (

let uu____20991 = (

let uu____20998 = (

let uu____20999 = (

let uu____21010 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____21010)))
in (FStar_SMTEncoding_Util.mkForall uu____20999))
in ((uu____20998), (FStar_Pervasives_Native.Some ("Correspondence of recursive function to instrumented version")), ((Prims.strcat "@fuel_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____20991))
in (

let eqn_g' = (

let uu____21024 = (

let uu____21031 = (

let uu____21032 = (

let uu____21043 = (

let uu____21044 = (

let uu____21049 = (

let uu____21050 = (

let uu____21057 = (

let uu____21060 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____21060)::vars_tm)
in ((g), (uu____21057)))
in (FStar_SMTEncoding_Util.mkApp uu____21050))
in ((gsapp), (uu____21049)))
in (FStar_SMTEncoding_Util.mkEq uu____21044))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____21043)))
in (FStar_SMTEncoding_Util.mkForall uu____21032))
in ((uu____21031), (FStar_Pervasives_Native.Some ("Fuel irrelevance")), ((Prims.strcat "@fuel_irrelevance_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21024))
in (

let uu____21083 = (

let uu____21092 = (encode_binders FStar_Pervasives_Native.None formals env02)
in (match (uu____21092) with
| (vars1, v_guards, env4, binder_decls1, uu____21121) -> begin
(

let vars_tm1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars1)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm1)))
in (

let tok_corr = (

let tok_app = (

let uu____21146 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____21146 ((fuel)::vars1)))
in (

let uu____21151 = (

let uu____21158 = (

let uu____21159 = (

let uu____21170 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars1), (uu____21170)))
in (FStar_SMTEncoding_Util.mkForall uu____21159))
in ((uu____21158), (FStar_Pervasives_Native.Some ("Fuel token correspondence")), ((Prims.strcat "fuel_token_correspondence_" gtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____21151)))
in (

let uu____21191 = (

let uu____21198 = (encode_term_pred FStar_Pervasives_Native.None tres env4 gapp)
in (match (uu____21198) with
| (g_typing, d3) -> begin
(

let uu____21211 = (

let uu____21214 = (

let uu____21215 = (

let uu____21222 = (

let uu____21223 = (

let uu____21234 = (

let uu____21235 = (

let uu____21240 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____21240), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____21235))
in ((((gapp)::[])::[]), ((fuel)::vars1), (uu____21234)))
in (FStar_SMTEncoding_Util.mkForall uu____21223))
in ((uu____21222), (FStar_Pervasives_Native.Some ("Typing correspondence of token to term")), ((Prims.strcat "token_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21215))
in (uu____21214)::[])
in ((d3), (uu____21211)))
end))
in (match (uu____21191) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls1 aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____21083) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env02))
end)))))
end))))))))))
end));
)
end));
)
end))
end))
in (

let uu____21305 = (

let uu____21318 = (FStar_List.zip3 gtoks1 typs2 bindings1)
in (FStar_List.fold_left (fun uu____21397 uu____21398 -> (match (((uu____21397), (uu____21398))) with
| ((decls2, eqns, env01), (gtok, ty, lb)) -> begin
(

let uu____21553 = (encode_one_binding env01 gtok ty lb)
in (match (uu____21553) with
| (decls', eqns', env02) -> begin
(((decls')::decls2), ((FStar_List.append eqns' eqns)), (env02))
end))
end)) (((decls1)::[]), ([]), (env0)) uu____21318))
in (match (uu____21305) with
| (decls2, eqns, env01) -> begin
(

let uu____21626 = (

let isDeclFun = (fun uu___138_21638 -> (match (uu___138_21638) with
| FStar_SMTEncoding_Term.DeclFun (uu____21639) -> begin
true
end
| uu____21650 -> begin
false
end))
in (

let uu____21651 = (FStar_All.pipe_right decls2 FStar_List.flatten)
in (FStar_All.pipe_right uu____21651 (FStar_List.partition isDeclFun))))
in (match (uu____21626) with
| (prefix_decls, rest) -> begin
(

let eqns1 = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns1))), (env01)))
end))
end))))
end))))))
in (

let uu____21691 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___139_21695 -> (match (uu___139_21695) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____21696 -> begin
false
end)))) || (FStar_All.pipe_right typs1 (FStar_Util.for_some (fun t -> (

let uu____21702 = ((FStar_Syntax_Util.is_pure_or_ghost_function t) || (FStar_TypeChecker_Env.is_reifiable_function env1.tcenv t))
in (FStar_All.pipe_left Prims.op_Negation uu____21702))))))
in (match (uu____21691) with
| true -> begin
((decls1), (env1))
end
| uu____21711 -> begin
(FStar_All.try_with (fun uu___174_21719 -> (match (()) with
| () -> begin
(match ((not (is_rec))) with
| true -> begin
(encode_non_rec_lbdef bindings typs1 toks1 env1)
end
| uu____21732 -> begin
(encode_rec_lbdefs bindings typs1 toks1 env1)
end)
end)) (fun uu___173_21734 -> (match (uu___173_21734) with
| Inner_let_rec -> begin
((decls1), (env1))
end)))
end))))))))
end))
end))
end)) (fun uu___169_21746 -> (match (uu___169_21746) with
| Let_rec_unencodeable -> begin
(

let msg = (

let uu____21754 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____21754 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end)))))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let nm = (

let uu____21803 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____21803) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____21807 = (encode_sigelt' env se)
in (match (uu____21807) with
| (g, env1) -> begin
(

let g1 = (match (g) with
| [] -> begin
(

let uu____21823 = (

let uu____21824 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____21824))
in (uu____21823)::[])
end
| uu____21825 -> begin
(

let uu____21826 = (

let uu____21829 = (

let uu____21830 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____21830))
in (uu____21829)::g)
in (

let uu____21831 = (

let uu____21834 = (

let uu____21835 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____21835))
in (uu____21834)::[])
in (FStar_List.append uu____21826 uu____21831)))
end)
in ((g1), (env1)))
end))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let is_opaque_to_smt = (fun t -> (

let uu____21848 = (

let uu____21849 = (FStar_Syntax_Subst.compress t)
in uu____21849.FStar_Syntax_Syntax.n)
in (match (uu____21848) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____21853)) -> begin
(Prims.op_Equality s "opaque_to_smt")
end
| uu____21854 -> begin
false
end)))
in (

let is_uninterpreted_by_smt = (fun t -> (

let uu____21859 = (

let uu____21860 = (FStar_Syntax_Subst.compress t)
in uu____21860.FStar_Syntax_Syntax.n)
in (match (uu____21859) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____21864)) -> begin
(Prims.op_Equality s "uninterpreted_by_smt")
end
| uu____21865 -> begin
false
end)))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____21870) -> begin
(failwith "impossible -- removed by tc.fs")
end
| FStar_Syntax_Syntax.Sig_pragma (uu____21875) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_main (uu____21878) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____21881) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____21896) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____21900 = (

let uu____21901 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____21901 Prims.op_Negation))
in (match (uu____21900) with
| true -> begin
(([]), (env))
end
| uu____21910 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____21927 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((ed.FStar_Syntax_Syntax.binders), (tm), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end))
in (

let encode_action = (fun env1 a -> (

let uu____21947 = (new_term_constant_and_tok_from_lid env1 a.FStar_Syntax_Syntax.action_name)
in (match (uu____21947) with
| (aname, atok, env2) -> begin
(

let uu____21963 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____21963) with
| (formals, uu____21981) -> begin
(

let uu____21994 = (

let uu____21999 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____21999 env2))
in (match (uu____21994) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____22011 = (

let uu____22012 = (

let uu____22023 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____22039 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____22023), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____22012))
in (uu____22011)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action token")))))::[])
in (

let uu____22052 = (

let aux = (fun uu____22104 uu____22105 -> (match (((uu____22104), (uu____22105))) with
| ((bv, uu____22157), (env3, acc_sorts, acc)) -> begin
(

let uu____22195 = (gen_term_var env3 bv)
in (match (uu____22195) with
| (xxsym, xx, env4) -> begin
((env4), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::acc_sorts), ((xx)::acc))
end))
end))
in (FStar_List.fold_right aux formals ((env2), ([]), ([]))))
in (match (uu____22052) with
| (uu____22267, xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (

let a_eq = (

let uu____22290 = (

let uu____22297 = (

let uu____22298 = (

let uu____22309 = (

let uu____22310 = (

let uu____22315 = (mk_Apply tm xs_sorts)
in ((app), (uu____22315)))
in (FStar_SMTEncoding_Util.mkEq uu____22310))
in ((((app)::[])::[]), (xs_sorts), (uu____22309)))
in (FStar_SMTEncoding_Util.mkForall uu____22298))
in ((uu____22297), (FStar_Pervasives_Native.Some ("Action equality")), ((Prims.strcat aname "_equality"))))
in (FStar_SMTEncoding_Util.mkAssume uu____22290))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____22335 = (

let uu____22342 = (

let uu____22343 = (

let uu____22354 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____22354)))
in (FStar_SMTEncoding_Util.mkForall uu____22343))
in ((uu____22342), (FStar_Pervasives_Native.Some ("Action token correspondence")), ((Prims.strcat aname "_token_correspondence"))))
in (FStar_SMTEncoding_Util.mkAssume uu____22335))))
in ((env2), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____22373 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____22373) with
| (env1, decls2) -> begin
(((FStar_List.flatten decls2)), (env1))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22401, uu____22402) when (FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid) -> begin
(

let uu____22403 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____22403) with
| (tname, ttok, env1) -> begin
(([]), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22420, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let will_encode_definition = (

let uu____22426 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___140_22430 -> (match (uu___140_22430) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____22431) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____22436) -> begin
true
end
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____22437 -> begin
false
end))))
in (not (uu____22426)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____22444 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____22446 = (

let uu____22453 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_uninterpreted_by_smt))
in (encode_top_level_val uu____22453 env fv t quals))
in (match (uu____22446) with
| (decls, env1) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____22468 = (

let uu____22471 = (primitive_type_axioms env1.tcenv lid tname tsym)
in (FStar_List.append decls uu____22471))
in ((uu____22468), (env1)))))
end)))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, f) -> begin
(

let uu____22479 = (FStar_Syntax_Subst.open_univ_vars us f)
in (match (uu____22479) with
| (uu____22488, f1) -> begin
(

let uu____22490 = (encode_formula f1 env)
in (match (uu____22490) with
| (f2, decls) -> begin
(

let g = (

let uu____22504 = (

let uu____22505 = (

let uu____22512 = (

let uu____22515 = (

let uu____22516 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____22516))
in FStar_Pervasives_Native.Some (uu____22515))
in (

let uu____22517 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in ((f2), (uu____22512), (uu____22517))))
in (FStar_SMTEncoding_Util.mkAssume uu____22505))
in (uu____22504)::[])
in (((FStar_List.append decls g)), (env)))
end))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____22523) when ((FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) || (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_opaque_to_smt))) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let uu____22535 = (FStar_Util.fold_map (fun env1 lb -> (

let lid = (

let uu____22553 = (

let uu____22556 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____22556.FStar_Syntax_Syntax.fv_name)
in uu____22553.FStar_Syntax_Syntax.v)
in (

let uu____22557 = (

let uu____22558 = (FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____22558))
in (match (uu____22557) with
| true -> begin
(

let val_decl = (

let uu___175_22586 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___175_22586.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Irreducible)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___175_22586.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___175_22586.FStar_Syntax_Syntax.sigattrs})
in (

let uu____22591 = (encode_sigelt' env1 val_decl)
in (match (uu____22591) with
| (decls, env2) -> begin
((env2), (decls))
end)))
end
| uu____22602 -> begin
((env1), ([]))
end)))) env (FStar_Pervasives_Native.snd lbs))
in (match (uu____22535) with
| (env1, decls) -> begin
(((FStar_List.flatten decls)), (env1))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((uu____22619, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t1); FStar_Syntax_Syntax.lbunivs = uu____22621; FStar_Syntax_Syntax.lbtyp = uu____22622; FStar_Syntax_Syntax.lbeff = uu____22623; FStar_Syntax_Syntax.lbdef = uu____22624})::[]), uu____22625) when (FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid) -> begin
(

let uu____22644 = (new_term_constant_and_tok_from_lid env b2t1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____22644) with
| (tname, ttok, env1) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let b2t_x = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (

let valid_b2t_x = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b2t_x)::[])))
in (

let decls = (

let uu____22673 = (

let uu____22676 = (

let uu____22677 = (

let uu____22684 = (

let uu____22685 = (

let uu____22696 = (

let uu____22697 = (

let uu____22702 = (FStar_SMTEncoding_Util.mkApp (((FStar_Pervasives_Native.snd FStar_SMTEncoding_Term.boxBoolFun)), ((x)::[])))
in ((valid_b2t_x), (uu____22702)))
in (FStar_SMTEncoding_Util.mkEq uu____22697))
in ((((b2t_x)::[])::[]), ((xx)::[]), (uu____22696)))
in (FStar_SMTEncoding_Util.mkForall uu____22685))
in ((uu____22684), (FStar_Pervasives_Native.Some ("b2t def")), ("b2t_def")))
in (FStar_SMTEncoding_Util.mkAssume uu____22677))
in (uu____22676)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None))))::uu____22673)
in ((decls), (env1)))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____22735, uu____22736) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___141_22745 -> (match (uu___141_22745) with
| FStar_Syntax_Syntax.Discriminator (uu____22746) -> begin
true
end
| uu____22747 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____22750, lids) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____22761 = (

let uu____22762 = (FStar_List.hd l.FStar_Ident.ns)
in uu____22762.FStar_Ident.idText)
in (Prims.op_Equality uu____22761 "Prims"))))) && (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___142_22766 -> (match (uu___142_22766) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____22767 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____22771) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___143_22788 -> (match (uu___143_22788) with
| FStar_Syntax_Syntax.Projector (uu____22789) -> begin
true
end
| uu____22794 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____22797 = (try_lookup_free_var env l)
in (match (uu____22797) with
| FStar_Pervasives_Native.Some (uu____22804) -> begin
(([]), (env))
end
| FStar_Pervasives_Native.None -> begin
(

let se1 = (

let uu___176_22808 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l); FStar_Syntax_Syntax.sigquals = uu___176_22808.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___176_22808.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___176_22808.FStar_Syntax_Syntax.sigattrs})
in (encode_sigelt env se1))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____22815) -> begin
(encode_top_level_let env ((is_rec), (bindings)) se.FStar_Syntax_Syntax.sigquals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____22833) -> begin
(

let uu____22842 = (encode_sigelts env ses)
in (match (uu____22842) with
| (g, env1) -> begin
(

let uu____22859 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___144_22882 -> (match (uu___144_22882) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = uu____22883; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("inversion axiom"); FStar_SMTEncoding_Term.assumption_name = uu____22884; FStar_SMTEncoding_Term.assumption_fact_ids = uu____22885}) -> begin
false
end
| uu____22888 -> begin
true
end))))
in (match (uu____22859) with
| (g', inversions) -> begin
(

let uu____22903 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___145_22924 -> (match (uu___145_22924) with
| FStar_SMTEncoding_Term.DeclFun (uu____22925) -> begin
true
end
| uu____22936 -> begin
false
end))))
in (match (uu____22903) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env1))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____22954, tps, k, uu____22957, datas) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___146_22974 -> (match (uu___146_22974) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____22975 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____22984 = c
in (match (uu____22984) with
| (name, args, uu____22989, uu____22990, uu____22991) -> begin
(

let uu____22996 = (

let uu____22997 = (

let uu____23008 = (FStar_All.pipe_right args (FStar_List.map (fun uu____23025 -> (match (uu____23025) with
| (uu____23032, sort, uu____23034) -> begin
sort
end))))
in ((name), (uu____23008), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____22997))
in (uu____22996)::[])
end))
end
| uu____23039 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____23061 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____23067 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____23067 FStar_Option.isNone)))))
in (match (uu____23061) with
| true -> begin
[]
end
| uu____23098 -> begin
(

let uu____23099 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____23099) with
| (xxsym, xx) -> begin
(

let uu____23108 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____23147 l -> (match (uu____23147) with
| (out, decls) -> begin
(

let uu____23167 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____23167) with
| (uu____23178, data_t) -> begin
(

let uu____23180 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____23180) with
| (args, res) -> begin
(

let indices = (

let uu____23226 = (

let uu____23227 = (FStar_Syntax_Subst.compress res)
in uu____23227.FStar_Syntax_Syntax.n)
in (match (uu____23226) with
| FStar_Syntax_Syntax.Tm_app (uu____23238, indices) -> begin
indices
end
| uu____23260 -> begin
[]
end))
in (

let env1 = (FStar_All.pipe_right args (FStar_List.fold_left (fun env1 uu____23284 -> (match (uu____23284) with
| (x, uu____23290) -> begin
(

let uu____23291 = (

let uu____23292 = (

let uu____23299 = (mk_term_projector_name l x)
in ((uu____23299), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____23292))
in (push_term_var env1 x uu____23291))
end)) env))
in (

let uu____23302 = (encode_args indices env1)
in (match (uu____23302) with
| (indices1, decls') -> begin
((match ((Prims.op_disEquality (FStar_List.length indices1) (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____23326 -> begin
()
end);
(

let eqs = (

let uu____23328 = (FStar_List.map2 (fun v1 a -> (

let uu____23344 = (

let uu____23349 = (FStar_SMTEncoding_Util.mkFreeV v1)
in ((uu____23349), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____23344))) vars indices1)
in (FStar_All.pipe_right uu____23328 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____23352 = (

let uu____23353 = (

let uu____23358 = (

let uu____23359 = (

let uu____23364 = (mk_data_tester env1 l xx)
in ((uu____23364), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____23359))
in ((out), (uu____23358)))
in (FStar_SMTEncoding_Util.mkOr uu____23353))
in ((uu____23352), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____23108) with
| (data_ax, decls) -> begin
(

let uu____23377 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____23377) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____23388 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____23388 xx tapp))
end
| uu____23391 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____23392 = (

let uu____23399 = (

let uu____23400 = (

let uu____23411 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____23426 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____23411), (uu____23426))))
in (FStar_SMTEncoding_Util.mkForall uu____23400))
in (

let uu____23441 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in ((uu____23399), (FStar_Pervasives_Native.Some ("inversion axiom")), (uu____23441))))
in (FStar_SMTEncoding_Util.mkAssume uu____23392)))
in (FStar_List.append decls ((fuel_guarded_inversion)::[])))
end))
end))
end))
end)))
in (

let uu____23444 = (

let uu____23457 = (

let uu____23458 = (FStar_Syntax_Subst.compress k)
in uu____23458.FStar_Syntax_Syntax.n)
in (match (uu____23457) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____23503 -> begin
((tps), (k))
end))
in (match (uu____23444) with
| (formals, res) -> begin
(

let uu____23526 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____23526) with
| (formals1, res1) -> begin
(

let uu____23537 = (encode_binders FStar_Pervasives_Native.None formals1 env)
in (match (uu____23537) with
| (vars, guards, env', binder_decls, uu____23562) -> begin
(

let uu____23575 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____23575) with
| (tname, ttok, env1) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____23594 = (

let uu____23601 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____23601)))
in (FStar_SMTEncoding_Util.mkApp uu____23594))
in (

let uu____23610 = (

let tname_decl = (

let uu____23620 = (

let uu____23621 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____23653 -> (match (uu____23653) with
| (n1, s) -> begin
(((Prims.strcat tname n1)), (s), (false))
end))))
in (

let uu____23666 = (varops.next_id ())
in ((tname), (uu____23621), (FStar_SMTEncoding_Term.Term_sort), (uu____23666), (false))))
in (constructor_or_logic_type_decl uu____23620))
in (

let uu____23675 = (match (vars) with
| [] -> begin
(

let uu____23688 = (

let uu____23689 = (

let uu____23692 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_45 -> FStar_Pervasives_Native.Some (_0_45)) uu____23692))
in (push_free_var env1 t tname uu____23689))
in (([]), (uu____23688)))
end
| uu____23699 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("token"))))
in (

let ttok_fresh = (

let uu____23708 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____23708))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____23722 = (

let uu____23729 = (

let uu____23730 = (

let uu____23745 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (FStar_Pervasives_Native.None), (vars), (uu____23745)))
in (FStar_SMTEncoding_Util.mkForall' uu____23730))
in ((uu____23729), (FStar_Pervasives_Native.Some ("name-token correspondence")), ((Prims.strcat "token_correspondence_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____23722))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env1)))))))
end)
in (match (uu____23675) with
| (tok_decls, env2) -> begin
(((FStar_List.append tname_decl tok_decls)), (env2))
end)))
in (match (uu____23610) with
| (decls, env2) -> begin
(

let kindingAx = (

let uu____23785 = (encode_term_pred FStar_Pervasives_Native.None res1 env' tapp)
in (match (uu____23785) with
| (k1, decls1) -> begin
(

let karr = (match (((FStar_List.length formals1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____23803 = (

let uu____23804 = (

let uu____23811 = (

let uu____23812 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____23812))
in ((uu____23811), (FStar_Pervasives_Native.Some ("kinding")), ((Prims.strcat "pre_kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____23804))
in (uu____23803)::[])
end
| uu____23815 -> begin
[]
end)
in (

let uu____23816 = (

let uu____23819 = (

let uu____23822 = (

let uu____23823 = (

let uu____23830 = (

let uu____23831 = (

let uu____23842 = (FStar_SMTEncoding_Util.mkImp ((guard), (k1)))
in ((((tapp)::[])::[]), (vars), (uu____23842)))
in (FStar_SMTEncoding_Util.mkForall uu____23831))
in ((uu____23830), (FStar_Pervasives_Native.None), ((Prims.strcat "kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____23823))
in (uu____23822)::[])
in (FStar_List.append karr uu____23819))
in (FStar_List.append decls1 uu____23816)))
end))
in (

let aux = (

let uu____23858 = (

let uu____23861 = (inversion_axioms tapp vars)
in (

let uu____23864 = (

let uu____23867 = (pretype_axiom env2 tapp vars)
in (uu____23867)::[])
in (FStar_List.append uu____23861 uu____23864)))
in (FStar_List.append kindingAx uu____23858))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env2)))))
end)))))
end))
end))
end))
end))))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____23874, uu____23875, uu____23876, uu____23877, uu____23878) when (FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____23886, t, uu____23888, n_tps, uu____23890) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____23898 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____23898) with
| (ddconstrsym, ddtok, env1) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____23915 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____23915) with
| (formals, t_res) -> begin
(

let uu____23950 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____23950) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____23964 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____23964) with
| (vars, guards, env', binder_decls, names1) -> begin
(

let fields = (FStar_All.pipe_right names1 (FStar_List.mapi (fun n1 x -> (

let projectible = true
in (

let uu____24034 = (mk_term_projector_name d x)
in ((uu____24034), (FStar_SMTEncoding_Term.Term_sort), (projectible)))))))
in (

let datacons = (

let uu____24036 = (

let uu____24055 = (varops.next_id ())
in ((ddconstrsym), (fields), (FStar_SMTEncoding_Term.Term_sort), (uu____24055), (true)))
in (FStar_All.pipe_right uu____24036 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____24094 = (encode_term_pred FStar_Pervasives_Native.None t env1 ddtok_tm)
in (match (uu____24094) with
| (tok_typing, decls3) -> begin
(

let tok_typing1 = (match (fields) with
| (uu____24106)::uu____24107 -> begin
(

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (mk_Apply ddtok_tm ((ff)::[]))
in (

let vtok_app_r = (mk_Apply f ((((ddtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let uu____24152 = (

let uu____24163 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____24163)))
in (FStar_SMTEncoding_Util.mkForall uu____24152))))))
end
| uu____24188 -> begin
tok_typing
end)
in (

let uu____24197 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____24197) with
| (vars', guards', env'', decls_formals, uu____24222) -> begin
(

let uu____24235 = (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (encode_term_pred (FStar_Pervasives_Native.Some (fuel_tm)) t_res env'' dapp1)))
in (match (uu____24235) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____24266 -> begin
(

let uu____24273 = (

let uu____24274 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____24274))
in (uu____24273)::[])
end)
in (

let encode_elim = (fun uu____24284 -> (

let uu____24285 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____24285) with
| (head1, args) -> begin
(

let uu____24328 = (

let uu____24329 = (FStar_Syntax_Subst.compress head1)
in uu____24329.FStar_Syntax_Syntax.n)
in (match (uu____24328) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____24339; FStar_Syntax_Syntax.vars = uu____24340}, uu____24341) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____24347 = (encode_args args env')
in (match (uu____24347) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____24390 -> begin
(

let uu____24391 = (

let uu____24392 = (

let uu____24397 = (

let uu____24398 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____24398))
in ((uu____24397), (orig_arg.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____24392))
in (FStar_Exn.raise uu____24391))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____24414 = (

let uu____24415 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____24415))
in (match (uu____24414) with
| true -> begin
(

let uu____24428 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____24428)::[])
end
| uu____24429 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____24430 = (

let uu____24443 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____24493 uu____24494 -> (match (((uu____24493), (uu____24494))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____24589 = (

let uu____24596 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____24596))
in (match (uu____24589) with
| (uu____24609, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____24617 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____24617)::eqns_or_guards)
end
| uu____24618 -> begin
(

let uu____24619 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____24619)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____24443))
in (match (uu____24430) with
| (uu____24634, arg_vars, elim_eqns_or_guards, uu____24637) -> begin
(

let arg_vars1 = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_Util.mkApp ((encoded_head), (arg_vars1)))
in (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (s_fuel_tm)) dapp1 ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars1)
in (

let typing_inversion = (

let uu____24667 = (

let uu____24674 = (

let uu____24675 = (

let uu____24686 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____24697 = (

let uu____24698 = (

let uu____24703 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____24703)))
in (FStar_SMTEncoding_Util.mkImp uu____24698))
in ((((ty_pred)::[])::[]), (uu____24686), (uu____24697))))
in (FStar_SMTEncoding_Util.mkForall uu____24675))
in ((uu____24674), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____24667))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____24726 = (varops.fresh "x")
in ((uu____24726), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____24728 = (

let uu____24735 = (

let uu____24736 = (

let uu____24747 = (

let uu____24752 = (

let uu____24755 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____24755)::[])
in (uu____24752)::[])
in (

let uu____24760 = (

let uu____24761 = (

let uu____24766 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____24767 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____24766), (uu____24767))))
in (FStar_SMTEncoding_Util.mkImp uu____24761))
in ((uu____24747), ((x)::[]), (uu____24760))))
in (FStar_SMTEncoding_Util.mkForall uu____24736))
in (

let uu____24786 = (varops.mk_unique "lextop")
in ((uu____24735), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____24786))))
in (FStar_SMTEncoding_Util.mkAssume uu____24728))))
end
| uu____24789 -> begin
(

let prec = (

let uu____24793 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____24820 -> begin
(

let uu____24821 = (

let uu____24822 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____24822 dapp1))
in (uu____24821)::[])
end))))
in (FStar_All.pipe_right uu____24793 FStar_List.flatten))
in (

let uu____24829 = (

let uu____24836 = (

let uu____24837 = (

let uu____24848 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____24859 = (

let uu____24860 = (

let uu____24865 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____24865)))
in (FStar_SMTEncoding_Util.mkImp uu____24860))
in ((((ty_pred)::[])::[]), (uu____24848), (uu____24859))))
in (FStar_SMTEncoding_Util.mkForall uu____24837))
in ((uu____24836), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____24829)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____24886 = (encode_args args env')
in (match (uu____24886) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____24929 -> begin
(

let uu____24930 = (

let uu____24931 = (

let uu____24936 = (

let uu____24937 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____24937))
in ((uu____24936), (orig_arg.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____24931))
in (FStar_Exn.raise uu____24930))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____24953 = (

let uu____24954 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____24954))
in (match (uu____24953) with
| true -> begin
(

let uu____24967 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____24967)::[])
end
| uu____24968 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____24969 = (

let uu____24982 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____25032 uu____25033 -> (match (((uu____25032), (uu____25033))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____25128 = (

let uu____25135 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____25135))
in (match (uu____25128) with
| (uu____25148, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____25156 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____25156)::eqns_or_guards)
end
| uu____25157 -> begin
(

let uu____25158 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____25158)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____24982))
in (match (uu____24969) with
| (uu____25173, arg_vars, elim_eqns_or_guards, uu____25176) -> begin
(

let arg_vars1 = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_Util.mkApp ((encoded_head), (arg_vars1)))
in (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (s_fuel_tm)) dapp1 ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars1)
in (

let typing_inversion = (

let uu____25206 = (

let uu____25213 = (

let uu____25214 = (

let uu____25225 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25236 = (

let uu____25237 = (

let uu____25242 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____25242)))
in (FStar_SMTEncoding_Util.mkImp uu____25237))
in ((((ty_pred)::[])::[]), (uu____25225), (uu____25236))))
in (FStar_SMTEncoding_Util.mkForall uu____25214))
in ((uu____25213), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25206))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____25265 = (varops.fresh "x")
in ((uu____25265), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____25267 = (

let uu____25274 = (

let uu____25275 = (

let uu____25286 = (

let uu____25291 = (

let uu____25294 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____25294)::[])
in (uu____25291)::[])
in (

let uu____25299 = (

let uu____25300 = (

let uu____25305 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____25306 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____25305), (uu____25306))))
in (FStar_SMTEncoding_Util.mkImp uu____25300))
in ((uu____25286), ((x)::[]), (uu____25299))))
in (FStar_SMTEncoding_Util.mkForall uu____25275))
in (

let uu____25325 = (varops.mk_unique "lextop")
in ((uu____25274), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____25325))))
in (FStar_SMTEncoding_Util.mkAssume uu____25267))))
end
| uu____25328 -> begin
(

let prec = (

let uu____25332 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____25359 -> begin
(

let uu____25360 = (

let uu____25361 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____25361 dapp1))
in (uu____25360)::[])
end))))
in (FStar_All.pipe_right uu____25332 FStar_List.flatten))
in (

let uu____25368 = (

let uu____25375 = (

let uu____25376 = (

let uu____25387 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25398 = (

let uu____25399 = (

let uu____25404 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____25404)))
in (FStar_SMTEncoding_Util.mkImp uu____25399))
in ((((ty_pred)::[])::[]), (uu____25387), (uu____25398))))
in (FStar_SMTEncoding_Util.mkForall uu____25376))
in ((uu____25375), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25368)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| uu____25423 -> begin
((

let uu____25425 = (

let uu____25426 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____25427 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____25426 uu____25427)))
in (FStar_Errors.warn se.FStar_Syntax_Syntax.sigrng uu____25425));
(([]), ([]));
)
end))
end)))
in (

let uu____25432 = (encode_elim ())
in (match (uu____25432) with
| (decls2, elim) -> begin
(

let g = (

let uu____25452 = (

let uu____25455 = (

let uu____25458 = (

let uu____25461 = (

let uu____25464 = (

let uu____25465 = (

let uu____25476 = (

let uu____25479 = (

let uu____25480 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____25480))
in FStar_Pervasives_Native.Some (uu____25479))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____25476)))
in FStar_SMTEncoding_Term.DeclFun (uu____25465))
in (uu____25464)::[])
in (

let uu____25485 = (

let uu____25488 = (

let uu____25491 = (

let uu____25494 = (

let uu____25497 = (

let uu____25500 = (

let uu____25503 = (

let uu____25504 = (

let uu____25511 = (

let uu____25512 = (

let uu____25523 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____25523)))
in (FStar_SMTEncoding_Util.mkForall uu____25512))
in ((uu____25511), (FStar_Pervasives_Native.Some ("equality for proxy")), ((Prims.strcat "equality_tok_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____25504))
in (

let uu____25536 = (

let uu____25539 = (

let uu____25540 = (

let uu____25547 = (

let uu____25548 = (

let uu____25559 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____25570 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____25559), (uu____25570))))
in (FStar_SMTEncoding_Util.mkForall uu____25548))
in ((uu____25547), (FStar_Pervasives_Native.Some ("data constructor typing intro")), ((Prims.strcat "data_typing_intro_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____25540))
in (uu____25539)::[])
in (uu____25503)::uu____25536))
in ((FStar_SMTEncoding_Util.mkAssume ((tok_typing1), (FStar_Pervasives_Native.Some ("typing for data constructor proxy")), ((Prims.strcat "typing_tok_" ddtok)))))::uu____25500)
in (FStar_List.append uu____25497 elim))
in (FStar_List.append decls_pred uu____25494))
in (FStar_List.append decls_formals uu____25491))
in (FStar_List.append proxy_fresh uu____25488))
in (FStar_List.append uu____25461 uu____25485)))
in (FStar_List.append decls3 uu____25458))
in (FStar_List.append decls2 uu____25455))
in (FStar_List.append binder_decls uu____25452))
in (((FStar_List.append datacons g)), (env1)))
end)))))
end))
end)))
end))))))))
end)))
end))
end)))
end)))
end))))
and encode_sigelts : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____25616 se -> (match (uu____25616) with
| (g, env1) -> begin
(

let uu____25636 = (encode_sigelt env1 se)
in (match (uu____25636) with
| (g', env2) -> begin
(((FStar_List.append g g')), (env2))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____25695 -> (match (uu____25695) with
| (i, decls, env1) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____25727) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env1))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____25733 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____25733) with
| true -> begin
(

let uu____25734 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____25735 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____25736 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____25734 uu____25735 uu____25736))))
end
| uu____25737 -> begin
()
end));
(

let uu____25738 = (encode_term t1 env1)
in (match (uu____25738) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____25754 = (

let uu____25761 = (

let uu____25762 = (

let uu____25763 = (FStar_Util.digest_of_string t_hash)
in (Prims.strcat uu____25763 (Prims.strcat "_" (Prims.string_of_int i))))
in (Prims.strcat "x_" uu____25762))
in (new_term_constant_from_string env1 x uu____25761))
in (match (uu____25754) with
| (xxsym, xx, env') -> begin
(

let t2 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel FStar_Pervasives_Native.None xx t)
in (

let caption = (

let uu____25779 = (FStar_Options.log_queries ())
in (match (uu____25779) with
| true -> begin
(

let uu____25782 = (

let uu____25783 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____25784 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____25785 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____25783 uu____25784 uu____25785))))
in FStar_Pervasives_Native.Some (uu____25782))
end
| uu____25786 -> begin
FStar_Pervasives_Native.None
end))
in (

let ax = (

let a_name = (Prims.strcat "binder_" xxsym)
in (FStar_SMTEncoding_Util.mkAssume ((t2), (FStar_Pervasives_Native.Some (a_name)), (a_name))))
in (

let g = (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun (((xxsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((ax)::[])))
in (((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))))))
end)))
end));
))
end
| FStar_TypeChecker_Env.Binding_lid (x, (uu____25801, t)) -> begin
(

let t_norm = (whnf env1 t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____25815 = (encode_free_var false env1 fv t t_norm [])
in (match (uu____25815) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| FStar_TypeChecker_Env.Binding_sig_inst (uu____25838, se, uu____25840) -> begin
(

let uu____25845 = (encode_sigelt env1 se)
in (match (uu____25845) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end
| FStar_TypeChecker_Env.Binding_sig (uu____25862, se) -> begin
(

let uu____25868 = (encode_sigelt env1 se)
in (match (uu____25868) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____25885 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____25885) with
| (uu____25908, decls, env1) -> begin
((decls), (env1))
end))))


let encode_labels : 'Auu____25923 'Auu____25924 . ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____25924 * 'Auu____25923) Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl Prims.list) = (fun labs -> (

let prefix1 = (FStar_All.pipe_right labs (FStar_List.map (fun uu____25992 -> (match (uu____25992) with
| (l, uu____26004, uu____26005) -> begin
FStar_SMTEncoding_Term.DeclFun ((((FStar_Pervasives_Native.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (FStar_Pervasives_Native.None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____26051 -> (match (uu____26051) with
| (l, uu____26065, uu____26066) -> begin
(

let uu____26075 = (FStar_All.pipe_left (fun _0_46 -> FStar_SMTEncoding_Term.Echo (_0_46)) (FStar_Pervasives_Native.fst l))
in (

let uu____26076 = (

let uu____26079 = (

let uu____26080 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____26080))
in (uu____26079)::[])
in (uu____26075)::uu____26076))
end))))
in ((prefix1), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____26102 = (

let uu____26105 = (

let uu____26106 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____26109 = (

let uu____26110 = (FStar_TypeChecker_Env.current_module tcenv)
in (FStar_All.pipe_right uu____26110 FStar_Ident.string_of_lid))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____26106; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true; current_module_name = uu____26109}))
in (uu____26105)::[])
in (FStar_ST.op_Colon_Equals last_env uu____26102)))


let get_env : FStar_Ident.lident  ->  FStar_TypeChecker_Env.env  ->  env_t = (fun cmn tcenv -> (

let uu____26137 = (FStar_ST.op_Bang last_env)
in (match (uu____26137) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____26159 -> begin
(

let uu___177_26162 = e
in (

let uu____26163 = (FStar_Ident.string_of_lid cmn)
in {bindings = uu___177_26162.bindings; depth = uu___177_26162.depth; tcenv = tcenv; warn = uu___177_26162.warn; cache = uu___177_26162.cache; nolabels = uu___177_26162.nolabels; use_zfuel_name = uu___177_26162.use_zfuel_name; encode_non_total_function_typ = uu___177_26162.encode_non_total_function_typ; current_module_name = uu____26163}))
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____26168 = (FStar_ST.op_Bang last_env)
in (match (uu____26168) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____26189)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl1))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____26214 -> (

let uu____26215 = (FStar_ST.op_Bang last_env)
in (match (uu____26215) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd1)::tl1 -> begin
(

let refs = (FStar_Util.smap_copy hd1.cache)
in (

let top = (

let uu___178_26244 = hd1
in {bindings = uu___178_26244.bindings; depth = uu___178_26244.depth; tcenv = uu___178_26244.tcenv; warn = uu___178_26244.warn; cache = refs; nolabels = uu___178_26244.nolabels; use_zfuel_name = uu___178_26244.use_zfuel_name; encode_non_total_function_typ = uu___178_26244.encode_non_total_function_typ; current_module_name = uu___178_26244.current_module_name})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd1)::tl1))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____26266 -> (

let uu____26267 = (FStar_ST.op_Bang last_env)
in (match (uu____26267) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____26288)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env tl1)
end)))


let init : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> ((init_env tcenv);
(FStar_SMTEncoding_Z3.init ());
(FStar_SMTEncoding_Z3.giveZ3 ((FStar_SMTEncoding_Term.DefPrelude)::[]));
))


let push : Prims.string  ->  Prims.unit = (fun msg -> ((push_env ());
(varops.push ());
(FStar_SMTEncoding_Z3.push msg);
))


let pop : Prims.string  ->  Prims.unit = (fun msg -> ((pop_env ());
(varops.pop ());
(FStar_SMTEncoding_Z3.pop msg);
))


let open_fact_db_tags : env_t  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env -> [])


let place_decl_in_fact_dbs : env_t  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl = (fun env fact_db_ids d -> (match (((fact_db_ids), (d))) with
| ((uu____26354)::uu____26355, FStar_SMTEncoding_Term.Assume (a)) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___179_26363 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___179_26363.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = uu___179_26363.FStar_SMTEncoding_Term.assumption_caption; FStar_SMTEncoding_Term.assumption_name = uu___179_26363.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids}))
end
| uu____26364 -> begin
d
end))


let fact_dbs_for_lid : env_t  ->  FStar_Ident.lid  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env lid -> (

let uu____26381 = (

let uu____26384 = (

let uu____26385 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_SMTEncoding_Term.Namespace (uu____26385))
in (

let uu____26386 = (open_fact_db_tags env)
in (uu____26384)::uu____26386))
in (FStar_SMTEncoding_Term.Name (lid))::uu____26381))


let encode_top_level_facts : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env se -> (

let fact_db_ids = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.collect (fact_dbs_for_lid env)))
in (

let uu____26410 = (encode_sigelt env se)
in (match (uu____26410) with
| (g, env1) -> begin
(

let g1 = (FStar_All.pipe_right g (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)))
in ((g1), (env1)))
end))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> (

let uu____26448 = (FStar_Options.log_queries ())
in (match (uu____26448) with
| true -> begin
(

let uu____26451 = (

let uu____26452 = (

let uu____26453 = (

let uu____26454 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____26454 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____26453))
in FStar_SMTEncoding_Term.Caption (uu____26452))
in (uu____26451)::decls)
end
| uu____26463 -> begin
decls
end)))
in (

let env = (

let uu____26465 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____26465 tcenv))
in (

let uu____26466 = (encode_top_level_facts env se)
in (match (uu____26466) with
| (decls, env1) -> begin
((set_env env1);
(

let uu____26480 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____26480));
)
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____26492 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____26494 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____26494) with
| true -> begin
(

let uu____26495 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) Prims.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____26495))
end
| uu____26496 -> begin
()
end));
(

let env = (get_env modul.FStar_Syntax_Syntax.name tcenv)
in (

let encode_signature = (fun env1 ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____26530 se -> (match (uu____26530) with
| (g, env2) -> begin
(

let uu____26550 = (encode_top_level_facts env2 se)
in (match (uu____26550) with
| (g', env3) -> begin
(((FStar_List.append g g')), (env3))
end))
end)) (([]), (env1)))))
in (

let uu____26573 = (encode_signature (

let uu___180_26582 = env
in {bindings = uu___180_26582.bindings; depth = uu___180_26582.depth; tcenv = uu___180_26582.tcenv; warn = false; cache = uu___180_26582.cache; nolabels = uu___180_26582.nolabels; use_zfuel_name = uu___180_26582.use_zfuel_name; encode_non_total_function_typ = uu___180_26582.encode_non_total_function_typ; current_module_name = uu___180_26582.current_module_name}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____26573) with
| (decls, env1) -> begin
(

let caption = (fun decls1 -> (

let uu____26599 = (FStar_Options.log_queries ())
in (match (uu____26599) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls1) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____26603 -> begin
decls1
end)))
in ((set_env (

let uu___181_26607 = env1
in {bindings = uu___181_26607.bindings; depth = uu___181_26607.depth; tcenv = uu___181_26607.tcenv; warn = true; cache = uu___181_26607.cache; nolabels = uu___181_26607.nolabels; use_zfuel_name = uu___181_26607.use_zfuel_name; encode_non_total_function_typ = uu___181_26607.encode_non_total_function_typ; current_module_name = uu___181_26607.current_module_name}));
(

let uu____26609 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____26609) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____26610 -> begin
()
end));
(

let decls1 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls1));
))
end))));
)))


let encode_query : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____26664 = (

let uu____26665 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____26665.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____26664));
(

let env = (

let uu____26667 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____26667 tcenv))
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____26679 = (

let rec aux = (fun bindings1 -> (match (bindings1) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____26714 = (aux rest)
in (match (uu____26714) with
| (out, rest1) -> begin
(

let t = (

let uu____26744 = (FStar_Syntax_Util.destruct_typ_as_formula x.FStar_Syntax_Syntax.sort)
in (match (uu____26744) with
| FStar_Pervasives_Native.Some (uu____26749) -> begin
(

let uu____26750 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Util.refine uu____26750 x.FStar_Syntax_Syntax.sort))
end
| uu____26751 -> begin
x.FStar_Syntax_Syntax.sort
end))
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
in (

let uu____26755 = (

let uu____26758 = (FStar_Syntax_Syntax.mk_binder (

let uu___182_26761 = x
in {FStar_Syntax_Syntax.ppname = uu___182_26761.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___182_26761.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in (uu____26758)::out)
in ((uu____26755), (rest1)))))
end))
end
| uu____26766 -> begin
(([]), (bindings1))
end))
in (

let uu____26773 = (aux bindings)
in (match (uu____26773) with
| (closing, bindings1) -> begin
(

let uu____26798 = (FStar_Syntax_Util.close_forall_no_univs (FStar_List.rev closing) q)
in ((uu____26798), (bindings1)))
end)))
in (match (uu____26679) with
| (q1, bindings1) -> begin
(

let uu____26821 = (

let uu____26826 = (FStar_List.filter (fun uu___147_26831 -> (match (uu___147_26831) with
| FStar_TypeChecker_Env.Binding_sig (uu____26832) -> begin
false
end
| uu____26839 -> begin
true
end)) bindings1)
in (encode_env_bindings env uu____26826))
in (match (uu____26821) with
| (env_decls, env1) -> begin
((

let uu____26857 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____26857) with
| true -> begin
(

let uu____26858 = (FStar_Syntax_Print.term_to_string q1)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____26858))
end
| uu____26859 -> begin
()
end));
(

let uu____26860 = (encode_formula q1 env1)
in (match (uu____26860) with
| (phi, qdecls) -> begin
(

let uu____26881 = (

let uu____26886 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____26886 phi))
in (match (uu____26881) with
| (labels, phi1) -> begin
(

let uu____26903 = (encode_labels labels)
in (match (uu____26903) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____26940 = (

let uu____26947 = (FStar_SMTEncoding_Util.mkNot phi1)
in (

let uu____26948 = (varops.mk_unique "@query")
in ((uu____26947), (FStar_Pervasives_Native.Some ("query")), (uu____26948))))
in (FStar_SMTEncoding_Util.mkAssume uu____26940))
in (

let suffix = (FStar_List.append ((FStar_SMTEncoding_Term.Echo ("<labels>"))::[]) (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("</labels>"))::(FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end))
end));
)
end))
end))));
))


let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun tcenv q -> (

let env = (

let uu____26967 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____26967 tcenv))
in ((FStar_SMTEncoding_Z3.push "query");
(

let uu____26969 = (encode_formula q env)
in (match (uu____26969) with
| (f, uu____26975) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____26977) -> begin
true
end
| uu____26982 -> begin
false
end);
)
end));
)))





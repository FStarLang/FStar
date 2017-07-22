
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


let vargs : 'Auu____71 'Auu____72 'Auu____73 . (('Auu____73, 'Auu____72) FStar_Util.either * 'Auu____71) Prims.list  ->  (('Auu____73, 'Auu____72) FStar_Util.either * 'Auu____71) Prims.list = (fun args -> (FStar_List.filter (fun uu___102_119 -> (match (uu___102_119) with
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


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a1 = (

let uu___126_221 = a
in (

let uu____222 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____222; FStar_Syntax_Syntax.index = uu___126_221.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___126_221.FStar_Syntax_Syntax.sort}))
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
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let __proj__Mkvarops_t__item__push : varops_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__push
end))


let __proj__Mkvarops_t__item__pop : varops_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__pop
end))


let __proj__Mkvarops_t__item__mark : varops_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__mark
end))


let __proj__Mkvarops_t__item__reset_mark : varops_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__reset_mark
end))


let __proj__Mkvarops_t__item__commit_mark : varops_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__commit_mark
end))


let __proj__Mkvarops_t__item__new_var : varops_t  ->  FStar_Ident.ident  ->  Prims.int  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__new_var
end))


let __proj__Mkvarops_t__item__new_fvar : varops_t  ->  FStar_Ident.lident  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__new_fvar
end))


let __proj__Mkvarops_t__item__fresh : varops_t  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__fresh
end))


let __proj__Mkvarops_t__item__string_const : varops_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__string_const
end))


let __proj__Mkvarops_t__item__next_id : varops_t  ->  Prims.unit  ->  Prims.int = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__next_id
end))


let __proj__Mkvarops_t__item__mk_unique : varops_t  ->  Prims.string  ->  Prims.string = (fun projectee -> (match (projectee) with
| {push = __fname__push; pop = __fname__pop; mark = __fname__mark; reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark; new_var = __fname__new_var; new_fvar = __fname__new_fvar; fresh = __fname__fresh; string_const = __fname__string_const; next_id = __fname__next_id; mk_unique = __fname__mk_unique} -> begin
__fname__mk_unique
end))


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun uu____946 -> (

let uu____947 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____950 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((uu____947), (uu____950)))))
in (

let scopes = (

let uu____970 = (

let uu____981 = (new_scope ())
in (uu____981)::[])
in (FStar_Util.mk_ref uu____970))
in (

let mk_unique = (fun y -> (

let y1 = (escape y)
in (

let y2 = (

let uu____1022 = (

let uu____1025 = (FStar_ST.read scopes)
in (FStar_Util.find_map uu____1025 (fun uu____1059 -> (match (uu____1059) with
| (names1, uu____1071) -> begin
(FStar_Util.smap_try_find names1 y1)
end))))
in (match (uu____1022) with
| FStar_Pervasives_Native.None -> begin
y1
end
| FStar_Pervasives_Native.Some (uu____1080) -> begin
((FStar_Util.incr ctr);
(

let uu____1085 = (

let uu____1086 = (

let uu____1087 = (FStar_ST.read ctr)
in (Prims.string_of_int uu____1087))
in (Prims.strcat "__" uu____1086))
in (Prims.strcat y1 uu____1085));
)
end))
in (

let top_scope = (

let uu____1093 = (

let uu____1102 = (FStar_ST.read scopes)
in (FStar_List.hd uu____1102))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1093))
in ((FStar_Util.smap_add top_scope y2 true);
y2;
)))))
in (

let new_var = (fun pp rn -> (FStar_All.pipe_left mk_unique (Prims.strcat pp.FStar_Ident.idText (Prims.strcat "__" (Prims.string_of_int rn)))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id1 = (fun uu____1162 -> ((FStar_Util.incr ctr);
(FStar_ST.read ctr);
))
in (

let fresh1 = (fun pfx -> (

let uu____1173 = (

let uu____1174 = (next_id1 ())
in (FStar_All.pipe_left Prims.string_of_int uu____1174))
in (FStar_Util.format2 "%s_%s" pfx uu____1173)))
in (

let string_const = (fun s -> (

let uu____1179 = (

let uu____1182 = (FStar_ST.read scopes)
in (FStar_Util.find_map uu____1182 (fun uu____1216 -> (match (uu____1216) with
| (uu____1227, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____1179) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let id = (next_id1 ())
in (

let f = (

let uu____1240 = (FStar_SMTEncoding_Util.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1240))
in (

let top_scope = (

let uu____1244 = (

let uu____1253 = (FStar_ST.read scopes)
in (FStar_List.hd uu____1253))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1244))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push1 = (fun uu____1302 -> (

let uu____1303 = (

let uu____1314 = (new_scope ())
in (

let uu____1323 = (FStar_ST.read scopes)
in (uu____1314)::uu____1323))
in (FStar_ST.write scopes uu____1303)))
in (

let pop1 = (fun uu____1369 -> (

let uu____1370 = (

let uu____1381 = (FStar_ST.read scopes)
in (FStar_List.tl uu____1381))
in (FStar_ST.write scopes uu____1370)))
in (

let mark1 = (fun uu____1427 -> (push1 ()))
in (

let reset_mark1 = (fun uu____1431 -> (pop1 ()))
in (

let commit_mark1 = (fun uu____1435 -> (

let uu____1436 = (FStar_ST.read scopes)
in (match (uu____1436) with
| ((hd1, hd2))::((next1, next2))::tl1 -> begin
((FStar_Util.smap_fold hd1 (fun key value v1 -> (FStar_Util.smap_add next1 key value)) ());
(FStar_Util.smap_fold hd2 (fun key value v1 -> (FStar_Util.smap_add next2 key value)) ());
(FStar_ST.write scopes ((((next1), (next2)))::tl1));
)
end
| uu____1544 -> begin
(failwith "Impossible")
end)))
in {push = push1; pop = pop1; mark = mark1; reset_mark = reset_mark1; commit_mark = commit_mark1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let uu___127_1559 = x
in (

let uu____1560 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____1560; FStar_Syntax_Syntax.index = uu___127_1559.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___127_1559.FStar_Syntax_Syntax.sort})))

type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____1594 -> begin
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
| uu____1632 -> begin
false
end))


let __proj__Binding_fvar__item___0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_0) -> begin
_0
end))


let binder_of_eithervar : 'Auu____1683 'Auu____1684 . 'Auu____1684  ->  ('Auu____1684 * 'Auu____1683 FStar_Pervasives_Native.option) = (fun v1 -> ((v1), (FStar_Pervasives_Native.None)))

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


let mk_cache_entry : 'Auu____1998 . 'Auu____1998  ->  Prims.string  ->  FStar_SMTEncoding_Term.sort Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  cache_entry = (fun env tsym cvar_sorts t_decls -> (

let names1 = (FStar_All.pipe_right t_decls (FStar_List.collect (fun uu___103_2032 -> (match (uu___103_2032) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(a.FStar_SMTEncoding_Term.assumption_name)::[]
end
| uu____2036 -> begin
[]
end))))
in {cache_symbol_name = tsym; cache_symbol_arg_sorts = cvar_sorts; cache_symbol_decls = t_decls; cache_symbol_assumption_names = names1}))


let use_cache_entry : cache_entry  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun ce -> (FStar_SMTEncoding_Term.RetainAssumptions (ce.cache_symbol_assumption_names))::[])


let print_env : env_t  ->  Prims.string = (fun e -> (

let uu____2047 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun uu___104_2057 -> (match (uu___104_2057) with
| Binding_var (x, uu____2059) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, uu____2061, uu____2062, uu____2063) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right uu____2047 (FStar_String.concat ", "))))


let lookup_binding : 'Auu____2080 . env_t  ->  (binding  ->  'Auu____2080 FStar_Pervasives_Native.option)  ->  'Auu____2080 FStar_Pervasives_Native.option = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string FStar_Pervasives_Native.option = (fun env t -> (

let uu____2110 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____2110) with
| true -> begin
(

let uu____2113 = (FStar_Syntax_Print.term_to_string t)
in FStar_Pervasives_Native.Some (uu____2113))
end
| uu____2114 -> begin
FStar_Pervasives_Native.None
end)))


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (

let uu____2128 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (uu____2128)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (Prims.strcat "@x" (Prims.string_of_int env.depth))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let uu___128_2146 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___128_2146.tcenv; warn = uu___128_2146.warn; cache = uu___128_2146.cache; nolabels = uu___128_2146.nolabels; use_zfuel_name = uu___128_2146.use_zfuel_name; encode_non_total_function_typ = uu___128_2146.encode_non_total_function_typ; current_module_name = uu___128_2146.current_module_name}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___129_2166 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___129_2166.depth; tcenv = uu___129_2166.tcenv; warn = uu___129_2166.warn; cache = uu___129_2166.cache; nolabels = uu___129_2166.nolabels; use_zfuel_name = uu___129_2166.use_zfuel_name; encode_non_total_function_typ = uu___129_2166.encode_non_total_function_typ; current_module_name = uu___129_2166.current_module_name}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___130_2190 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___130_2190.depth; tcenv = uu___130_2190.tcenv; warn = uu___130_2190.warn; cache = uu___130_2190.cache; nolabels = uu___130_2190.nolabels; use_zfuel_name = uu___130_2190.use_zfuel_name; encode_non_total_function_typ = uu___130_2190.encode_non_total_function_typ; current_module_name = uu___130_2190.current_module_name}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___131_2203 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = uu___131_2203.depth; tcenv = uu___131_2203.tcenv; warn = uu___131_2203.warn; cache = uu___131_2203.cache; nolabels = uu___131_2203.nolabels; use_zfuel_name = uu___131_2203.use_zfuel_name; encode_non_total_function_typ = uu___131_2203.encode_non_total_function_typ; current_module_name = uu___131_2203.current_module_name}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun uu___105_2229 -> (match (uu___105_2229) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
FStar_Pervasives_Native.Some (((b), (t)))
end
| uu____2242 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____2247 = (aux a)
in (match (uu____2247) with
| FStar_Pervasives_Native.None -> begin
(

let a2 = (unmangle a)
in (

let uu____2259 = (aux a2)
in (match (uu____2259) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2270 = (

let uu____2271 = (FStar_Syntax_Print.bv_to_string a2)
in (

let uu____2272 = (print_env env)
in (FStar_Util.format2 "Bound term variable not found (after unmangling): %s in environment: %s" uu____2271 uu____2272)))
in (failwith uu____2270))
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

let uu____2301 = (

let uu___132_2302 = env
in (

let uu____2303 = (

let uu____2306 = (

let uu____2307 = (

let uu____2320 = (

let uu____2323 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _0_39 -> FStar_Pervasives_Native.Some (_0_39)) uu____2323))
in ((x), (fname), (uu____2320), (FStar_Pervasives_Native.None)))
in Binding_fvar (uu____2307))
in (uu____2306)::env.bindings)
in {bindings = uu____2303; depth = uu___132_2302.depth; tcenv = uu___132_2302.tcenv; warn = uu___132_2302.warn; cache = uu___132_2302.cache; nolabels = uu___132_2302.nolabels; use_zfuel_name = uu___132_2302.use_zfuel_name; encode_non_total_function_typ = uu___132_2302.encode_non_total_function_typ; current_module_name = uu___132_2302.current_module_name}))
in ((fname), (ftok), (uu____2301))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) FStar_Pervasives_Native.option = (fun env a -> (lookup_binding env (fun uu___106_2367 -> (match (uu___106_2367) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
FStar_Pervasives_Native.Some (((t1), (t2), (t3)))
end
| uu____2406 -> begin
FStar_Pervasives_Native.None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (

let uu____2425 = (lookup_binding env (fun uu___107_2433 -> (match (uu___107_2433) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
FStar_Pervasives_Native.Some (())
end
| uu____2448 -> begin
FStar_Pervasives_Native.None
end)))
in (FStar_All.pipe_right uu____2425 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) = (fun env a -> (

let uu____2469 = (try_lookup_lid env a)
in (match (uu____2469) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2502 = (

let uu____2503 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____2503))
in (failwith uu____2502))
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  env_t = (fun env x fname ftok -> (

let uu___133_2555 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (FStar_Pervasives_Native.None))))::env.bindings; depth = uu___133_2555.depth; tcenv = uu___133_2555.tcenv; warn = uu___133_2555.warn; cache = uu___133_2555.cache; nolabels = uu___133_2555.nolabels; use_zfuel_name = uu___133_2555.use_zfuel_name; encode_non_total_function_typ = uu___133_2555.encode_non_total_function_typ; current_module_name = uu___133_2555.current_module_name}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let uu____2572 = (lookup_lid env x)
in (match (uu____2572) with
| (t1, t2, uu____2585) -> begin
(

let t3 = (

let uu____2595 = (

let uu____2602 = (

let uu____2605 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____2605)::[])
in ((f), (uu____2602)))
in (FStar_SMTEncoding_Util.mkApp uu____2595))
in (

let uu___134_2610 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (FStar_Pervasives_Native.Some (t3)))))::env.bindings; depth = uu___134_2610.depth; tcenv = uu___134_2610.tcenv; warn = uu___134_2610.warn; cache = uu___134_2610.cache; nolabels = uu___134_2610.nolabels; use_zfuel_name = uu___134_2610.use_zfuel_name; encode_non_total_function_typ = uu___134_2610.encode_non_total_function_typ; current_module_name = uu___134_2610.current_module_name}))
end)))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____2625 = (try_lookup_lid env l)
in (match (uu____2625) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| FStar_Pervasives_Native.Some (f) when env.use_zfuel_name -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____2674 -> begin
(match (sym) with
| FStar_Pervasives_Native.Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____2682, (fuel)::[]) -> begin
(

let uu____2686 = (

let uu____2687 = (

let uu____2688 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____2688 FStar_Pervasives_Native.fst))
in (FStar_Util.starts_with uu____2687 "fuel"))
in (match (uu____2686) with
| true -> begin
(

let uu____2691 = (

let uu____2692 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____2692 fuel))
in (FStar_All.pipe_left (fun _0_40 -> FStar_Pervasives_Native.Some (_0_40)) uu____2691))
end
| uu____2695 -> begin
FStar_Pervasives_Native.Some (t)
end))
end
| uu____2696 -> begin
FStar_Pervasives_Native.Some (t)
end)
end
| uu____2697 -> begin
FStar_Pervasives_Native.None
end)
end)
end)))


let lookup_free_var : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____2712 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____2712) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____2716 = (

let uu____2717 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____2717))
in (failwith uu____2716))
end)))


let lookup_free_var_name : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  Prims.string = (fun env a -> (

let uu____2730 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____2730) with
| (x, uu____2742, uu____2743) -> begin
x
end)))


let lookup_free_var_sym : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  (FStar_SMTEncoding_Term.op * FStar_SMTEncoding_Term.term Prims.list) = (fun env a -> (

let uu____2770 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____2770) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| FStar_Pervasives_Native.Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____2806; FStar_SMTEncoding_Term.rng = uu____2807}) when env.use_zfuel_name -> begin
((g), (zf))
end
| uu____2822 -> begin
(match (sym) with
| FStar_Pervasives_Native.None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| FStar_Pervasives_Native.Some (sym1) -> begin
(match (sym1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| uu____2846 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___108_2864 -> (match (uu___108_2864) with
| Binding_fvar (uu____2867, nm', tok, uu____2870) when (nm = nm') -> begin
tok
end
| uu____2879 -> begin
FStar_Pervasives_Native.None
end))))


let mkForall_fuel' : 'Auu____2886 . 'Auu____2886  ->  (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (fun n1 uu____2904 -> (match (uu____2904) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____2929 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____2934 = (FStar_Options.unthrottle_inductives ())
in (match (uu____2934) with
| true -> begin
(fallback ())
end
| uu____2935 -> begin
(

let uu____2936 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____2936) with
| (fsym, fterm) -> begin
(

let add_fuel1 = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____2967 -> begin
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

let uu____2988 = (add_fuel1 guards)
in (FStar_SMTEncoding_Util.mk_and_l uu____2988))
end
| uu____2991 -> begin
(

let uu____2992 = (add_fuel1 ((guard)::[]))
in (FStar_All.pipe_right uu____2992 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard1), (body'))))
end
| uu____2997 -> begin
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
| FStar_Syntax_Syntax.Tm_arrow (uu____3041) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____3054) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3061) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3062) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____3079) -> begin
true
end
| FStar_Syntax_Syntax.Tm_constant (uu____3096) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3098 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3098 FStar_Option.isNone))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____3116; FStar_Syntax_Syntax.vars = uu____3117}, uu____3118) -> begin
(

let uu____3139 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3139 FStar_Option.isNone))
end
| uu____3156 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____3165 = (

let uu____3166 = (FStar_Syntax_Util.un_uinst t)
in uu____3166.FStar_Syntax_Syntax.n)
in (match (uu____3165) with
| FStar_Syntax_Syntax.Tm_abs (uu____3169, uu____3170, FStar_Pervasives_Native.Some (rc)) -> begin
(((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___109_3191 -> (match (uu___109_3191) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____3192 -> begin
false
end)) rc.FStar_Syntax_Syntax.residual_flags))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3194 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3194 FStar_Option.isSome))
end
| uu____3211 -> begin
false
end)))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____3220 = (head_normal env t)
in (match (uu____3220) with
| true -> begin
t
end
| uu____3221 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____3234 = (

let uu____3235 = (FStar_Syntax_Syntax.null_binder t)
in (uu____3235)::[])
in (

let uu____3236 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.abs uu____3234 uu____3236 FStar_Pervasives_Native.None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((FStar_Pervasives_Native.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(

let uu____3276 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out uu____3276))
end
| s -> begin
(

let uu____3281 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out uu____3281))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___110_3299 -> (match (uu___110_3299) with
| FStar_SMTEncoding_Term.Var ("ApplyTT") -> begin
true
end
| FStar_SMTEncoding_Term.Var ("ApplyTF") -> begin
true
end
| uu____3300 -> begin
false
end))


let is_an_eta_expansion : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env vars body -> (

let rec check_partial_applications = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____3339; FStar_SMTEncoding_Term.rng = uu____3340})::[]), (x)::xs1) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(check_partial_applications f xs1)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____3363) -> begin
(

let uu____3372 = (((FStar_List.length args) = (FStar_List.length xs)) && (FStar_List.forall2 (fun a v1 -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v1)
end
| uu____3383 -> begin
false
end)) args (FStar_List.rev xs)))
in (match (uu____3372) with
| true -> begin
(tok_of_name env f)
end
| uu____3386 -> begin
FStar_Pervasives_Native.None
end))
end
| (uu____3387, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____3391 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (

let uu____3395 = (FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)
in (not (uu____3395))))))
in (match (uu____3391) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____3398 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____3399 -> begin
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
| uu____3629 -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun uu___111_3633 -> (match (uu___111_3633) with
| FStar_Const.Const_unit -> begin
FStar_SMTEncoding_Term.mk_Term_unit
end
| FStar_Const.Const_bool (true) -> begin
(FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
end
| FStar_Const.Const_bool (false) -> begin
(FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse)
end
| FStar_Const.Const_char (c) -> begin
(

let uu____3635 = (

let uu____3642 = (

let uu____3645 = (

let uu____3646 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt uu____3646))
in (uu____3645)::[])
in (("FStar.Char.Char"), (uu____3642)))
in (FStar_SMTEncoding_Util.mkApp uu____3635))
end
| FStar_Const.Const_int (i, FStar_Pervasives_Native.None) -> begin
(

let uu____3660 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____3660))
end
| FStar_Const.Const_int (i, FStar_Pervasives_Native.Some (uu____3662)) -> begin
(failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, uu____3678) -> begin
(

let uu____3683 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const uu____3683))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(

let uu____3688 = (

let uu____3689 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" uu____3689))
in (failwith uu____3688))
end))


let as_function_typ : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____3710) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_refine (uu____3723) -> begin
(

let uu____3730 = (FStar_Syntax_Util.unrefine t1)
in (aux true uu____3730))
end
| uu____3731 -> begin
(match (norm1) with
| true -> begin
(

let uu____3732 = (whnf env t1)
in (aux false uu____3732))
end
| uu____3733 -> begin
(

let uu____3734 = (

let uu____3735 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____3736 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____3735 uu____3736)))
in (failwith uu____3734))
end)
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| uu____3768 -> begin
(

let uu____3769 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____3769)))
end)))


let is_arithmetic_primitive : 'Auu____3786 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____3786 Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____3806)::(uu____3807)::[]) -> begin
(((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Subtraction)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____3811)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus)
end
| uu____3814 -> begin
false
end))


let isInteger : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
true
end
| uu____3836 -> begin
false
end))


let getInteger : FStar_Syntax_Syntax.term'  ->  Prims.int = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
(FStar_Util.int_of_string n1)
end
| uu____3852 -> begin
(failwith "Expected an Integer term")
end))


let is_BitVector_primitive : 'Auu____3859 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____3859) Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____3898))::(uu____3899)::(uu____3900)::[]) -> begin
((((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_and_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_xor_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_left_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_right_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_udiv_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mod_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____3951))::(uu____3952)::[]) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_to_nat_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| uu____3989 -> begin
false
end))


let rec encode_binders : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____4198 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4198) with
| true -> begin
(

let uu____4199 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____4199))
end
| uu____4200 -> begin
()
end));
(

let uu____4201 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____4285 b -> (match (uu____4285) with
| (vars, guards, env1, decls, names1) -> begin
(

let uu____4364 = (

let x = (unmangle (FStar_Pervasives_Native.fst b))
in (

let uu____4380 = (gen_term_var env1 x)
in (match (uu____4380) with
| (xxsym, xx, env') -> begin
(

let uu____4404 = (

let uu____4409 = (norm env1 x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____4409 env1 xx))
in (match (uu____4404) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____4364) with
| (v1, g, env2, decls', n1) -> begin
(((v1)::vars), ((g)::guards), (env2), ((FStar_List.append decls decls')), ((n1)::names1))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____4201) with
| (vars, guards, env1, decls, names1) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env1), (decls), ((FStar_List.rev names1)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____4568 = (encode_term t env)
in (match (uu____4568) with
| (t1, decls) -> begin
(

let uu____4579 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1)
in ((uu____4579), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____4590 = (encode_term t env)
in (match (uu____4590) with
| (t1, decls) -> begin
(match (fuel_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4605 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t1)
in ((uu____4605), (decls)))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____4607 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1)
in ((uu____4607), (decls)))
end)
end)))
and encode_arith_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.args  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun env head1 args_e -> (

let uu____4613 = (encode_args args_e env)
in (match (uu____4613) with
| (arg_tms, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____4632 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms1 -> (

let uu____4641 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____4641)))
in (

let binary = (fun arg_tms1 -> (

let uu____4654 = (

let uu____4655 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____4655))
in (

let uu____4656 = (

let uu____4657 = (

let uu____4658 = (FStar_List.tl arg_tms1)
in (FStar_List.hd uu____4658))
in (FStar_SMTEncoding_Term.unboxInt uu____4657))
in ((uu____4654), (uu____4656)))))
in (

let mk_default = (fun uu____4664 -> (

let uu____4665 = (lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____4665) with
| (fname, fuel_args) -> begin
(FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args arg_tms))))
end)))
in (

let mk_l = (fun op mk_args ts -> (

let uu____4716 = (FStar_Options.smtencoding_l_arith_native ())
in (match (uu____4716) with
| true -> begin
(

let uu____4717 = (

let uu____4718 = (mk_args ts)
in (op uu____4718))
in (FStar_All.pipe_right uu____4717 FStar_SMTEncoding_Term.boxInt))
end
| uu____4719 -> begin
(mk_default ())
end)))
in (

let mk_nl = (fun nm op ts -> (

let uu____4747 = (FStar_Options.smtencoding_nl_arith_wrapped ())
in (match (uu____4747) with
| true -> begin
(

let uu____4748 = (binary ts)
in (match (uu____4748) with
| (t1, t2) -> begin
(

let uu____4755 = (FStar_SMTEncoding_Util.mkApp ((nm), ((t1)::(t2)::[])))
in (FStar_All.pipe_right uu____4755 FStar_SMTEncoding_Term.boxInt))
end))
end
| uu____4758 -> begin
(

let uu____4759 = (FStar_Options.smtencoding_nl_arith_native ())
in (match (uu____4759) with
| true -> begin
(

let uu____4760 = (op (binary ts))
in (FStar_All.pipe_right uu____4760 FStar_SMTEncoding_Term.boxInt))
end
| uu____4761 -> begin
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

let uu____4891 = (

let uu____4900 = (FStar_List.tryFind (fun uu____4922 -> (match (uu____4922) with
| (l, uu____4932) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____4900 FStar_Util.must))
in (match (uu____4891) with
| (uu____4971, op) -> begin
(

let uu____4981 = (op arg_tms)
in ((uu____4981), (decls)))
end)))))))))))))))
end)))
and encode_BitVector_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.arg Prims.list  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun env head1 args_e -> (

let uu____4989 = (FStar_List.hd args_e)
in (match (uu____4989) with
| (tm_sz, uu____4997) -> begin
(

let sz = (getInteger tm_sz.FStar_Syntax_Syntax.n)
in (

let sz_key = (FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz))
in (

let sz_decls = (

let uu____5007 = (FStar_Util.smap_try_find env.cache sz_key)
in (match (uu____5007) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
[]
end
| FStar_Pervasives_Native.None -> begin
(

let t_decls = (FStar_SMTEncoding_Term.mkBvConstructor sz)
in ((

let uu____5015 = (mk_cache_entry env "" [] [])
in (FStar_Util.smap_add env.cache sz_key uu____5015));
t_decls;
))
end))
in (

let uu____5016 = (match (((head1.FStar_Syntax_Syntax.n), (args_e))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5036)::((sz_arg, uu____5038))::(uu____5039)::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) && (isInteger sz_arg.FStar_Syntax_Syntax.n)) -> begin
(

let uu____5088 = (

let uu____5091 = (FStar_List.tail args_e)
in (FStar_List.tail uu____5091))
in (

let uu____5094 = (

let uu____5097 = (getInteger sz_arg.FStar_Syntax_Syntax.n)
in FStar_Pervasives_Native.Some (uu____5097))
in ((uu____5088), (uu____5094))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5103)::((sz_arg, uu____5105))::(uu____5106)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) -> begin
(

let uu____5155 = (

let uu____5156 = (FStar_Syntax_Print.term_to_string sz_arg)
in (FStar_Util.format1 "Not a constant bitvector extend size: %s" uu____5156))
in (failwith uu____5155))
end
| uu____5165 -> begin
(

let uu____5172 = (FStar_List.tail args_e)
in ((uu____5172), (FStar_Pervasives_Native.None)))
end)
in (match (uu____5016) with
| (arg_tms, ext_sz) -> begin
(

let uu____5195 = (encode_args arg_tms env)
in (match (uu____5195) with
| (arg_tms1, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____5216 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms2 -> (

let uu____5225 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5225)))
in (

let unary_arith = (fun arg_tms2 -> (

let uu____5234 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxInt uu____5234)))
in (

let binary = (fun arg_tms2 -> (

let uu____5247 = (

let uu____5248 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5248))
in (

let uu____5249 = (

let uu____5250 = (

let uu____5251 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____5251))
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5250))
in ((uu____5247), (uu____5249)))))
in (

let binary_arith = (fun arg_tms2 -> (

let uu____5266 = (

let uu____5267 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5267))
in (

let uu____5268 = (

let uu____5269 = (

let uu____5270 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____5270))
in (FStar_SMTEncoding_Term.unboxInt uu____5269))
in ((uu____5266), (uu____5268)))))
in (

let mk_bv = (fun op mk_args resBox ts -> (

let uu____5319 = (

let uu____5320 = (mk_args ts)
in (op uu____5320))
in (FStar_All.pipe_right uu____5319 resBox)))
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

let uu____5410 = (

let uu____5413 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (FStar_SMTEncoding_Util.mkBvUext uu____5413))
in (

let uu____5415 = (

let uu____5418 = (

let uu____5419 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (sz + uu____5419))
in (FStar_SMTEncoding_Term.boxBitVec uu____5418))
in (mk_bv uu____5410 unary uu____5415 arg_tms2))))
in (

let to_int = (mk_bv FStar_SMTEncoding_Util.mkBvToNat unary FStar_SMTEncoding_Term.boxInt)
in (

let bv_to = (mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz) unary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let ops = (((FStar_Parser_Const.bv_and_lid), (bv_and)))::(((FStar_Parser_Const.bv_xor_lid), (bv_xor)))::(((FStar_Parser_Const.bv_or_lid), (bv_or)))::(((FStar_Parser_Const.bv_shift_left_lid), (bv_shl)))::(((FStar_Parser_Const.bv_shift_right_lid), (bv_shr)))::(((FStar_Parser_Const.bv_udiv_lid), (bv_udiv)))::(((FStar_Parser_Const.bv_mod_lid), (bv_mod)))::(((FStar_Parser_Const.bv_mul_lid), (bv_mul)))::(((FStar_Parser_Const.bv_ult_lid), (bv_ult)))::(((FStar_Parser_Const.bv_uext_lid), (bv_uext)))::(((FStar_Parser_Const.bv_to_nat_lid), (to_int)))::(((FStar_Parser_Const.nat_to_bv_lid), (bv_to)))::[]
in (

let uu____5594 = (

let uu____5603 = (FStar_List.tryFind (fun uu____5625 -> (match (uu____5625) with
| (l, uu____5635) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____5603 FStar_Util.must))
in (match (uu____5594) with
| (uu____5676, op) -> begin
(

let uu____5686 = (op arg_tms1)
in ((uu____5686), ((FStar_List.append sz_decls decls))))
end)))))))))))))))))))))
end))
end)))))
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____5697 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____5697) with
| true -> begin
(

let uu____5698 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____5699 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____5700 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____5698 uu____5699 uu____5700))))
end
| uu____5701 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____5706) -> begin
(

let uu____5731 = (

let uu____5732 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____5733 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____5734 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____5735 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5732 uu____5733 uu____5734 uu____5735)))))
in (failwith uu____5731))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____5740 = (

let uu____5741 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____5742 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____5743 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____5744 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5741 uu____5742 uu____5743 uu____5744)))))
in (failwith uu____5740))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____5750 = (

let uu____5751 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____5751))
in (failwith uu____5750))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, k, uu____5758) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____5800) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t1 = (lookup_term_var env x)
in ((t1), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v1) -> begin
(

let uu____5810 = (lookup_free_var env v1.FStar_Syntax_Syntax.fv_name)
in ((uu____5810), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____5813) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____5817) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____5823 = (encode_const c)
in ((uu____5823), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let module_name = env.current_module_name
in (

let uu____5845 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____5845) with
| (binders1, res) -> begin
(

let uu____5856 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____5856) with
| true -> begin
(

let uu____5861 = (encode_binders FStar_Pervasives_Native.None binders1 env)
in (match (uu____5861) with
| (vars, guards, env', decls, uu____5886) -> begin
(

let fsym = (

let uu____5904 = (varops.fresh "f")
in ((uu____5904), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____5907 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___135_5916 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___135_5916.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___135_5916.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___135_5916.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___135_5916.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___135_5916.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___135_5916.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___135_5916.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___135_5916.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___135_5916.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___135_5916.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___135_5916.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___135_5916.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___135_5916.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___135_5916.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___135_5916.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___135_5916.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___135_5916.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___135_5916.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___135_5916.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___135_5916.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___135_5916.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___135_5916.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___135_5916.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___135_5916.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___135_5916.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___135_5916.FStar_TypeChecker_Env.is_native_tactic}) res)
in (match (uu____5907) with
| (pre_opt, res_t) -> begin
(

let uu____5927 = (encode_term_pred FStar_Pervasives_Native.None res_t env' app)
in (match (uu____5927) with
| (res_pred, decls') -> begin
(

let uu____5938 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5951 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____5951), ([])))
end
| FStar_Pervasives_Native.Some (pre) -> begin
(

let uu____5955 = (encode_formula pre env')
in (match (uu____5955) with
| (guard, decls0) -> begin
(

let uu____5968 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____5968), (decls0)))
end))
end)
in (match (uu____5938) with
| (guards1, guard_decls) -> begin
(

let t_interp = (

let uu____5980 = (

let uu____5991 = (FStar_SMTEncoding_Util.mkImp ((guards1), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____5991)))
in (FStar_SMTEncoding_Util.mkForall uu____5980))
in (

let cvars = (

let uu____6009 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____6009 (FStar_List.filter (fun uu____6023 -> (match (uu____6023) with
| (x, uu____6029) -> begin
(x <> (FStar_Pervasives_Native.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____6048 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____6048) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____6056 = (

let uu____6057 = (

let uu____6064 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____6064)))
in (FStar_SMTEncoding_Util.mkApp uu____6057))
in ((uu____6056), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append guard_decls (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let tsym = (

let uu____6084 = (

let uu____6085 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____6085))
in (varops.mk_unique uu____6084))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars)
in (

let caption = (

let uu____6096 = (FStar_Options.log_queries ())
in (match (uu____6096) with
| true -> begin
(

let uu____6099 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in FStar_Pervasives_Native.Some (uu____6099))
end
| uu____6100 -> begin
FStar_Pervasives_Native.None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t1 = (

let uu____6107 = (

let uu____6114 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____6114)))
in (FStar_SMTEncoding_Util.mkApp uu____6107))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = (Prims.strcat "kinding_" tsym)
in (

let uu____6126 = (

let uu____6133 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____6133), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____6126)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t1)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t1)
in (

let pre_typing = (

let a_name = (Prims.strcat "pre_typing_" tsym)
in (

let uu____6154 = (

let uu____6161 = (

let uu____6162 = (

let uu____6173 = (

let uu____6174 = (

let uu____6179 = (

let uu____6180 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____6180))
in ((f_has_t), (uu____6179)))
in (FStar_SMTEncoding_Util.mkImp uu____6174))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____6173)))
in (mkForall_fuel uu____6162))
in ((uu____6161), (FStar_Pervasives_Native.Some ("pre-typing for functions")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6154)))
in (

let t_interp1 = (

let a_name = (Prims.strcat "interpretation_" tsym)
in (

let uu____6203 = (

let uu____6210 = (

let uu____6211 = (

let uu____6222 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____6222)))
in (FStar_SMTEncoding_Util.mkForall uu____6211))
in ((uu____6210), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6203)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp1)::[]))))
in ((

let uu____6247 = (mk_cache_entry env tsym cvar_sorts t_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____6247));
((t1), (t_decls));
)))))))))))))
end))))))
end))
end))
end)))))
end))
end
| uu____6250 -> begin
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

let uu____6262 = (

let uu____6269 = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____6269), (FStar_Pervasives_Native.Some ("Typing for non-total arrows")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6262)))
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

let uu____6281 = (

let uu____6288 = (

let uu____6289 = (

let uu____6300 = (

let uu____6301 = (

let uu____6306 = (

let uu____6307 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____6307))
in ((f_has_t), (uu____6306)))
in (FStar_SMTEncoding_Util.mkImp uu____6301))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____6300)))
in (mkForall_fuel uu____6289))
in ((uu____6288), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6281)))
in ((t1), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____6334) -> begin
(

let uu____6341 = (

let uu____6346 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____6346) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.pos = uu____6353; FStar_Syntax_Syntax.vars = uu____6354} -> begin
(

let uu____6361 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____6361) with
| (b, f1) -> begin
(

let uu____6386 = (

let uu____6387 = (FStar_List.hd b)
in (FStar_Pervasives_Native.fst uu____6387))
in ((uu____6386), (f1)))
end))
end
| uu____6396 -> begin
(failwith "impossible")
end))
in (match (uu____6341) with
| (x, f) -> begin
(

let uu____6407 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____6407) with
| (base_t, decls) -> begin
(

let uu____6418 = (gen_term_var env x)
in (match (uu____6418) with
| (x1, xtm, env') -> begin
(

let uu____6432 = (encode_formula f env')
in (match (uu____6432) with
| (refinement, decls') -> begin
(

let uu____6443 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____6443) with
| (fsym, fterm) -> begin
(

let tm_has_type_with_fuel = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (fterm)) xtm base_t)
in (

let encoding = (FStar_SMTEncoding_Util.mkAnd ((tm_has_type_with_fuel), (refinement)))
in (

let cvars = (

let uu____6459 = (

let uu____6462 = (FStar_SMTEncoding_Term.free_variables refinement)
in (

let uu____6469 = (FStar_SMTEncoding_Term.free_variables tm_has_type_with_fuel)
in (FStar_List.append uu____6462 uu____6469)))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____6459))
in (

let cvars1 = (FStar_All.pipe_right cvars (FStar_List.filter (fun uu____6502 -> (match (uu____6502) with
| (y, uu____6508) -> begin
((y <> x1) && (y <> fsym))
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

let uu____6541 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____6541) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____6549 = (

let uu____6550 = (

let uu____6557 = (FStar_All.pipe_right cvars1 (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____6557)))
in (FStar_SMTEncoding_Util.mkApp uu____6550))
in ((uu____6549), ((FStar_List.append decls (FStar_List.append decls' (use_cache_entry cache_entry))))))
end
| FStar_Pervasives_Native.None -> begin
(

let module_name = env.current_module_name
in (

let tsym = (

let uu____6578 = (

let uu____6579 = (

let uu____6580 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "_Tm_refine_" uu____6580))
in (Prims.strcat module_name uu____6579))
in (varops.mk_unique uu____6578))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars1)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let t1 = (

let uu____6594 = (

let uu____6601 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((tsym), (uu____6601)))
in (FStar_SMTEncoding_Util.mkApp uu____6594))
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

let uu____6616 = (

let uu____6623 = (

let uu____6624 = (

let uu____6635 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars1), (uu____6635)))
in (FStar_SMTEncoding_Util.mkForall uu____6624))
in ((uu____6623), (FStar_Pervasives_Native.Some ((Prims.strcat "haseq for " tsym))), ((Prims.strcat "haseq" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____6616))
in (

let t_valid = (

let xx = ((x1), (FStar_SMTEncoding_Term.Term_sort))
in (

let valid_t = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((t1)::[])))
in (

let uu____6661 = (

let uu____6668 = (

let uu____6669 = (

let uu____6680 = (

let uu____6681 = (

let uu____6686 = (

let uu____6687 = (

let uu____6698 = (FStar_SMTEncoding_Util.mkAnd ((x_has_base_t), (refinement)))
in (([]), ((xx)::[]), (uu____6698)))
in (FStar_SMTEncoding_Util.mkExists uu____6687))
in ((uu____6686), (valid_t)))
in (FStar_SMTEncoding_Util.mkIff uu____6681))
in ((((valid_t)::[])::[]), (cvars1), (uu____6680)))
in (FStar_SMTEncoding_Util.mkForall uu____6669))
in ((uu____6668), (FStar_Pervasives_Native.Some ("validity axiom for refinement")), ((Prims.strcat "ref_valid_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____6661))))
in (

let t_kinding = (

let uu____6736 = (

let uu____6743 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars1), (t_has_kind)))
in ((uu____6743), (FStar_Pervasives_Native.Some ("refinement kinding")), ((Prims.strcat "refinement_kinding_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____6736))
in (

let t_interp = (

let uu____6761 = (

let uu____6768 = (

let uu____6769 = (

let uu____6780 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars1), (uu____6780)))
in (FStar_SMTEncoding_Util.mkForall uu____6769))
in (

let uu____6803 = (

let uu____6806 = (FStar_Syntax_Print.term_to_string t0)
in FStar_Pervasives_Native.Some (uu____6806))
in ((uu____6768), (uu____6803), ((Prims.strcat "refinement_interpretation_" tsym)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6761))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_valid)::(t_interp)::(t_haseq1)::[])))
in ((

let uu____6813 = (mk_cache_entry env tsym cvar_sorts t_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____6813));
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

let uu____6843 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____6843))
in (

let uu____6844 = (encode_term_pred FStar_Pervasives_Native.None k env ttm)
in (match (uu____6844) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____6856 = (

let uu____6863 = (

let uu____6864 = (

let uu____6865 = (

let uu____6866 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____6866))
in (FStar_Util.format1 "uvar_typing_%s" uu____6865))
in (varops.mk_unique uu____6864))
in ((t_has_k), (FStar_Pervasives_Native.Some ("Uvar typing")), (uu____6863)))
in (FStar_SMTEncoding_Util.mkAssume uu____6856))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____6871) -> begin
(

let uu____6886 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____6886) with
| (head1, args_e) -> begin
(

let uu____6927 = (

let uu____6940 = (

let uu____6941 = (FStar_Syntax_Subst.compress head1)
in uu____6941.FStar_Syntax_Syntax.n)
in ((uu____6940), (args_e)))
in (match (uu____6927) with
| uu____6956 when (head_redex env head1) -> begin
(

let uu____6969 = (whnf env t)
in (encode_term uu____6969 env))
end
| uu____6970 when (is_arithmetic_primitive head1 args_e) -> begin
(encode_arith_term env head1 args_e)
end
| uu____6989 when (is_BitVector_primitive head1 args_e) -> begin
(encode_BitVector_term env head1 args_e)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7003; FStar_Syntax_Syntax.vars = uu____7004}, uu____7005), (uu____7006)::((v1, uu____7008))::((v2, uu____7010))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7061 = (encode_term v1 env)
in (match (uu____7061) with
| (v11, decls1) -> begin
(

let uu____7072 = (encode_term v2 env)
in (match (uu____7072) with
| (v21, decls2) -> begin
(

let uu____7083 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7083), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____7087)::((v1, uu____7089))::((v2, uu____7091))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7138 = (encode_term v1 env)
in (match (uu____7138) with
| (v11, decls1) -> begin
(

let uu____7149 = (encode_term v2 env)
in (match (uu____7149) with
| (v21, decls2) -> begin
(

let uu____7160 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7160), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____7163) -> begin
(

let e0 = (

let uu____7181 = (FStar_List.hd args_e)
in (FStar_TypeChecker_Util.reify_body_with_arg env.tcenv head1 uu____7181))
in ((

let uu____7189 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____7189) with
| true -> begin
(

let uu____7190 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" uu____7190))
end
| uu____7191 -> begin
()
end));
(

let e = (

let uu____7195 = (

let uu____7196 = (FStar_TypeChecker_Util.remove_reify e0)
in (

let uu____7197 = (FStar_List.tl args_e)
in (FStar_Syntax_Syntax.mk_Tm_app uu____7196 uu____7197)))
in (uu____7195 FStar_Pervasives_Native.None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____7206)), ((arg, uu____7208))::[]) -> begin
(encode_term arg env)
end
| uu____7233 -> begin
(

let uu____7246 = (encode_args args_e env)
in (match (uu____7246) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____7301 = (encode_term head1 env)
in (match (uu____7301) with
| (head2, decls') -> begin
(

let app_tm = (mk_Apply_args head2 args)
in (match (ht_opt) with
| FStar_Pervasives_Native.None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| FStar_Pervasives_Native.Some (formals, c) -> begin
(

let uu____7365 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____7365) with
| (formals1, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____7443 uu____7444 -> (match (((uu____7443), (uu____7444))) with
| ((bv, uu____7466), (a, uu____7468)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals1 args_e)
in (

let ty = (

let uu____7486 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____7486 (FStar_Syntax_Subst.subst subst1)))
in (

let uu____7491 = (encode_term_pred FStar_Pervasives_Native.None ty env app_tm)
in (match (uu____7491) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____7506 = (

let uu____7513 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____7522 = (

let uu____7523 = (

let uu____7524 = (

let uu____7525 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____7525))
in (Prims.strcat "partial_app_typing_" uu____7524))
in (varops.mk_unique uu____7523))
in ((uu____7513), (FStar_Pervasives_Native.Some ("Partial app typing")), (uu____7522))))
in (FStar_SMTEncoding_Util.mkAssume uu____7506))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____7542 = (lookup_free_var_sym env fv)
in (match (uu____7542) with
| (fname, fuel_args) -> begin
(

let tm = (FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args args))))
in ((tm), (decls)))
end)))
in (

let head2 = (FStar_Syntax_Subst.compress head1)
in (

let head_type = (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.pos = uu____7573; FStar_Syntax_Syntax.vars = uu____7574}, uu____7575) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7586; FStar_Syntax_Syntax.vars = uu____7587}, uu____7588) -> begin
(

let uu____7593 = (

let uu____7594 = (

let uu____7599 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____7599 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7594 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____7593))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____7629 = (

let uu____7630 = (

let uu____7635 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____7635 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____7630 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____7629))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____7664, (FStar_Util.Inl (t1), uu____7666), uu____7667) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____7716, (FStar_Util.Inr (c), uu____7718), uu____7719) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| uu____7768 -> begin
FStar_Pervasives_Native.None
end)
in (match (head_type) with
| FStar_Pervasives_Native.None -> begin
(encode_partial_app FStar_Pervasives_Native.None)
end
| FStar_Pervasives_Native.Some (head_type1) -> begin
(

let head_type2 = (

let uu____7795 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____7795))
in (

let uu____7796 = (curried_arrow_formals_comp head_type2)
in (match (uu____7796) with
| (formals, c) -> begin
(match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7812; FStar_Syntax_Syntax.vars = uu____7813}, uu____7814) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____7828 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (FStar_Pervasives_Native.Some (((formals), (c)))))
end
| uu____7841 -> begin
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

let uu____7877 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____7877) with
| (bs1, body1, opening) -> begin
(

let fallback = (fun uu____7900 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Imprecise function encoding"))))
in (

let uu____7907 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____7907), ((decl)::[]))))))
in (

let is_impure = (fun rc -> (

let uu____7914 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv rc.FStar_Syntax_Syntax.residual_effect)
in (FStar_All.pipe_right uu____7914 Prims.op_Negation)))
in (

let codomain_eff = (fun rc -> (

let res_typ = (match (rc.FStar_Syntax_Syntax.residual_typ) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7924 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____7924 FStar_Pervasives_Native.fst))
end
| FStar_Pervasives_Native.Some (t1) -> begin
t1
end)
in (match ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(

let uu____7944 = (FStar_Syntax_Syntax.mk_Total res_typ)
in FStar_Pervasives_Native.Some (uu____7944))
end
| uu____7945 -> begin
(match ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(

let uu____7948 = (FStar_Syntax_Syntax.mk_GTotal res_typ)
in FStar_Pervasives_Native.Some (uu____7948))
end
| uu____7949 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (lopt) with
| FStar_Pervasives_Native.None -> begin
((

let uu____7955 = (

let uu____7956 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____7956))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____7955));
(fallback ());
)
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____7958 = ((is_impure rc) && (

let uu____7960 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (not (uu____7960))))
in (match (uu____7958) with
| true -> begin
(fallback ())
end
| uu____7965 -> begin
(

let cache_size = (FStar_Util.smap_size env.cache)
in (

let uu____7967 = (encode_binders FStar_Pervasives_Native.None bs1 env)
in (match (uu____7967) with
| (vars, guards, envbody, decls, uu____7992) -> begin
(

let body2 = (FStar_TypeChecker_Util.reify_body env.tcenv body1)
in (

let uu____8006 = (encode_term body2 envbody)
in (match (uu____8006) with
| (body3, decls') -> begin
(

let uu____8017 = (

let uu____8026 = (codomain_eff rc)
in (match (uu____8026) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), ([]))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs1 c)
in (

let uu____8045 = (encode_term tfun env)
in (match (uu____8045) with
| (t1, decls1) -> begin
((FStar_Pervasives_Native.Some (t1)), (decls1))
end)))
end))
in (match (uu____8017) with
| (arrow_t_opt, decls'') -> begin
(

let key_body = (

let uu____8077 = (

let uu____8088 = (

let uu____8089 = (

let uu____8094 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____8094), (body3)))
in (FStar_SMTEncoding_Util.mkImp uu____8089))
in (([]), (vars), (uu____8088)))
in (FStar_SMTEncoding_Util.mkForall uu____8077))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let cvars1 = (match (arrow_t_opt) with
| FStar_Pervasives_Native.None -> begin
cvars
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____8106 = (

let uu____8109 = (FStar_SMTEncoding_Term.free_variables t1)
in (FStar_List.append uu____8109 cvars))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____8106))
end)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars1), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____8128 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____8128) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____8136 = (

let uu____8137 = (

let uu____8144 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((cache_entry.cache_symbol_name), (uu____8144)))
in (FStar_SMTEncoding_Util.mkApp uu____8137))
in ((uu____8136), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8155 = (is_an_eta_expansion env vars body3)
in (match (uu____8155) with
| FStar_Pervasives_Native.Some (t1) -> begin
(

let decls1 = (

let uu____8166 = (

let uu____8167 = (FStar_Util.smap_size env.cache)
in (uu____8167 = cache_size))
in (match (uu____8166) with
| true -> begin
[]
end
| uu____8170 -> begin
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

let uu____8183 = (

let uu____8184 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____8184))
in (varops.mk_unique uu____8183))
in (Prims.strcat module_name (Prims.strcat "_" fsym))))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let f = (

let uu____8191 = (

let uu____8198 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((fsym), (uu____8198)))
in (FStar_SMTEncoding_Util.mkApp uu____8191))
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

let uu____8216 = (

let uu____8217 = (

let uu____8224 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars1), (f_has_t)))
in ((uu____8224), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____8217))
in (uu____8216)::[])))
end)
in (

let interp_f = (

let a_name = (Prims.strcat "interpretation_" fsym)
in (

let uu____8237 = (

let uu____8244 = (

let uu____8245 = (

let uu____8256 = (FStar_SMTEncoding_Util.mkEq ((app), (body3)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars1)), (uu____8256)))
in (FStar_SMTEncoding_Util.mkForall uu____8245))
in ((uu____8244), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____8237)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[])))))
in ((

let uu____8273 = (mk_cache_entry env fsym cvar_sorts f_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____8273));
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
| FStar_Syntax_Syntax.Tm_let ((uu____8276, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____8277); FStar_Syntax_Syntax.lbunivs = uu____8278; FStar_Syntax_Syntax.lbtyp = uu____8279; FStar_Syntax_Syntax.lbeff = uu____8280; FStar_Syntax_Syntax.lbdef = uu____8281})::uu____8282), uu____8283) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____8309; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____8311; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____8332) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let uu____8352 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____8352), ((decl_e)::[])))));
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____8407 = (encode_term e1 env)
in (match (uu____8407) with
| (ee1, decls1) -> begin
(

let uu____8418 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) e2)
in (match (uu____8418) with
| (xs, e21) -> begin
(

let uu____8443 = (FStar_List.hd xs)
in (match (uu____8443) with
| (x1, uu____8457) -> begin
(

let env' = (push_term_var env x1 ee1)
in (

let uu____8459 = (encode_body e21 env')
in (match (uu____8459) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____8491 = (

let uu____8498 = (

let uu____8499 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_bv uu____8499))
in (gen_term_var env uu____8498))
in (match (uu____8491) with
| (scrsym, scr', env1) -> begin
(

let uu____8507 = (encode_term e env1)
in (match (uu____8507) with
| (scr, decls) -> begin
(

let uu____8518 = (

let encode_branch = (fun b uu____8543 -> (match (uu____8543) with
| (else_case, decls1) -> begin
(

let uu____8562 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____8562) with
| (p, w, br) -> begin
(

let uu____8588 = (encode_pat env1 p)
in (match (uu____8588) with
| (env0, pattern) -> begin
(

let guard = (pattern.guard scr')
in (

let projections = (pattern.projections scr')
in (

let env2 = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env2 uu____8625 -> (match (uu____8625) with
| (x, t) -> begin
(push_term_var env2 x t)
end)) env1))
in (

let uu____8632 = (match (w) with
| FStar_Pervasives_Native.None -> begin
((guard), ([]))
end
| FStar_Pervasives_Native.Some (w1) -> begin
(

let uu____8654 = (encode_term w1 env2)
in (match (uu____8654) with
| (w2, decls2) -> begin
(

let uu____8667 = (

let uu____8668 = (

let uu____8673 = (

let uu____8674 = (

let uu____8679 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w2), (uu____8679)))
in (FStar_SMTEncoding_Util.mkEq uu____8674))
in ((guard), (uu____8673)))
in (FStar_SMTEncoding_Util.mkAnd uu____8668))
in ((uu____8667), (decls2)))
end))
end)
in (match (uu____8632) with
| (guard1, decls2) -> begin
(

let uu____8692 = (encode_br br env2)
in (match (uu____8692) with
| (br1, decls3) -> begin
(

let uu____8705 = (FStar_SMTEncoding_Util.mkITE ((guard1), (br1), (else_case)))
in ((uu____8705), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end)))))
end))
end))
end))
in (FStar_List.fold_right encode_branch pats ((default_case), (decls))))
in (match (uu____8518) with
| (match_tm, decls1) -> begin
(

let uu____8724 = (FStar_SMTEncoding_Term.mkLet' (((((((scrsym), (FStar_SMTEncoding_Term.Term_sort))), (scr)))::[]), (match_tm)) FStar_Range.dummyRange)
in ((uu____8724), (decls1)))
end))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____8764 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____8764) with
| true -> begin
(

let uu____8765 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____8765))
end
| uu____8766 -> begin
()
end));
(

let uu____8767 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____8767) with
| (vars, pat_term) -> begin
(

let uu____8784 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____8837 v1 -> (match (uu____8837) with
| (env1, vars1) -> begin
(

let uu____8889 = (gen_term_var env1 v1)
in (match (uu____8889) with
| (xx, uu____8911, env2) -> begin
((env2), ((((v1), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars1))
end))
end)) ((env), ([]))))
in (match (uu____8784) with
| (env1, vars1) -> begin
(

let rec mk_guard = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (uu____8990) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_wild (uu____8991) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____8992) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____9000 = (

let uu____9005 = (encode_const c)
in ((scrutinee), (uu____9005)))
in (FStar_SMTEncoding_Util.mkEq uu____9000))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (

let tc_name = (FStar_TypeChecker_Env.typ_of_datacon env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____9026 = (FStar_TypeChecker_Env.datacons_of_typ env1.tcenv tc_name)
in (match (uu____9026) with
| (uu____9033, (uu____9034)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____9037 -> begin
(mk_data_tester env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
end)))
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____9070 -> (match (uu____9070) with
| (arg, uu____9078) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____9084 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____9084)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____9111) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____9142) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____9165 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____9209 -> (match (uu____9209) with
| (arg, uu____9223) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____9229 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____9229)))
end))))
in (FStar_All.pipe_right uu____9165 FStar_List.flatten))
end))
in (

let pat_term1 = (fun uu____9257 -> (encode_term pat_term env1))
in (

let pattern = {pat_vars = vars1; pat_term = pat_term1; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env1), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____9267 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____9305 uu____9306 -> (match (((uu____9305), (uu____9306))) with
| ((tms, decls), (t, uu____9342)) -> begin
(

let uu____9363 = (encode_term t env)
in (match (uu____9363) with
| (t1, decls') -> begin
(((t1)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____9267) with
| (l1, decls) -> begin
(((FStar_List.rev l1)), (decls))
end)))
and encode_function_type_as_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let list_elements1 = (fun e -> (

let uu____9420 = (FStar_Syntax_Util.list_elements e)
in (match (uu____9420) with
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

let uu____9441 = (

let uu____9456 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____9456 FStar_Syntax_Util.head_and_args))
in (match (uu____9441) with
| (head1, args) -> begin
(

let uu____9495 = (

let uu____9508 = (

let uu____9509 = (FStar_Syntax_Util.un_uinst head1)
in uu____9509.FStar_Syntax_Syntax.n)
in ((uu____9508), (args)))
in (match (uu____9495) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____9523, uu____9524))::((e, uu____9526))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
e
end
| uu____9561 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements1 p)
in (

let smt_pat_or1 = (fun t1 -> (

let uu____9597 = (

let uu____9612 = (FStar_Syntax_Util.unmeta t1)
in (FStar_All.pipe_right uu____9612 FStar_Syntax_Util.head_and_args))
in (match (uu____9597) with
| (head1, args) -> begin
(

let uu____9653 = (

let uu____9666 = (

let uu____9667 = (FStar_Syntax_Util.un_uinst head1)
in uu____9667.FStar_Syntax_Syntax.n)
in ((uu____9666), (args)))
in (match (uu____9653) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____9684))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
FStar_Pervasives_Native.Some (e)
end
| uu____9711 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (elts) with
| (t1)::[] -> begin
(

let uu____9733 = (smt_pat_or1 t1)
in (match (uu____9733) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____9749 = (list_elements1 e)
in (FStar_All.pipe_right uu____9749 (FStar_List.map (fun branch1 -> (

let uu____9767 = (list_elements1 branch1)
in (FStar_All.pipe_right uu____9767 (FStar_List.map one_pat)))))))
end
| uu____9778 -> begin
(

let uu____9783 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____9783)::[])
end))
end
| uu____9804 -> begin
(

let uu____9807 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____9807)::[])
end))))
in (

let uu____9828 = (

let uu____9847 = (

let uu____9848 = (FStar_Syntax_Subst.compress t)
in uu____9848.FStar_Syntax_Syntax.n)
in (match (uu____9847) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____9887 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____9887) with
| (binders1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____9930; FStar_Syntax_Syntax.effect_name = uu____9931; FStar_Syntax_Syntax.result_typ = uu____9932; FStar_Syntax_Syntax.effect_args = ((pre, uu____9934))::((post, uu____9936))::((pats, uu____9938))::[]; FStar_Syntax_Syntax.flags = uu____9939}) -> begin
(

let uu____9980 = (lemma_pats pats)
in ((binders1), (pre), (post), (uu____9980)))
end
| uu____9997 -> begin
(failwith "impos")
end)
end))
end
| uu____10016 -> begin
(failwith "Impos")
end))
in (match (uu____9828) with
| (binders, pre, post, patterns) -> begin
(

let env1 = (

let uu___136_10064 = env
in {bindings = uu___136_10064.bindings; depth = uu___136_10064.depth; tcenv = uu___136_10064.tcenv; warn = uu___136_10064.warn; cache = uu___136_10064.cache; nolabels = uu___136_10064.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___136_10064.encode_non_total_function_typ; current_module_name = uu___136_10064.current_module_name})
in (

let uu____10065 = (encode_binders FStar_Pervasives_Native.None binders env1)
in (match (uu____10065) with
| (vars, guards, env2, decls, uu____10090) -> begin
(

let uu____10103 = (

let uu____10116 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch1 -> (

let uu____10160 = (

let uu____10169 = (FStar_All.pipe_right branch1 (FStar_List.map (fun t1 -> (encode_term t1 env2))))
in (FStar_All.pipe_right uu____10169 FStar_List.unzip))
in (match (uu____10160) with
| (pats, decls1) -> begin
((pats), (decls1))
end)))))
in (FStar_All.pipe_right uu____10116 FStar_List.unzip))
in (match (uu____10103) with
| (pats, decls') -> begin
(

let decls'1 = (FStar_List.flatten decls')
in (

let env3 = (

let uu___137_10278 = env2
in {bindings = uu___137_10278.bindings; depth = uu___137_10278.depth; tcenv = uu___137_10278.tcenv; warn = uu___137_10278.warn; cache = uu___137_10278.cache; nolabels = true; use_zfuel_name = uu___137_10278.use_zfuel_name; encode_non_total_function_typ = uu___137_10278.encode_non_total_function_typ; current_module_name = uu___137_10278.current_module_name})
in (

let uu____10279 = (

let uu____10284 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____10284 env3))
in (match (uu____10279) with
| (pre1, decls'') -> begin
(

let uu____10291 = (

let uu____10296 = (FStar_Syntax_Util.unmeta post)
in (encode_formula uu____10296 env3))
in (match (uu____10291) with
| (post1, decls''') -> begin
(

let decls1 = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls'1) (FStar_List.append decls'' decls''')))
in (

let uu____10306 = (

let uu____10307 = (

let uu____10318 = (

let uu____10319 = (

let uu____10324 = (FStar_SMTEncoding_Util.mk_and_l ((pre1)::guards))
in ((uu____10324), (post1)))
in (FStar_SMTEncoding_Util.mkImp uu____10319))
in ((pats), (vars), (uu____10318)))
in (FStar_SMTEncoding_Util.mkForall uu____10307))
in ((uu____10306), (decls1))))
end))
end))))
end))
end)))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug1 = (fun phi1 -> (

let uu____10343 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____10343) with
| true -> begin
(

let uu____10344 = (FStar_Syntax_Print.tag_of_term phi1)
in (

let uu____10345 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____10344 uu____10345)))
end
| uu____10346 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____10378 = (FStar_Util.fold_map (fun decls x -> (

let uu____10406 = (encode_term (FStar_Pervasives_Native.fst x) env)
in (match (uu____10406) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____10378) with
| (decls, args) -> begin
(

let uu____10435 = (

let uu___138_10436 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___138_10436.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___138_10436.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____10435), (decls)))
end)))
in (

let const_op = (fun f r uu____10467 -> (

let uu____10480 = (f r)
in ((uu____10480), ([]))))
in (

let un_op = (fun f l -> (

let uu____10499 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____10499)))
in (

let bin_op = (fun f uu___112_10515 -> (match (uu___112_10515) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____10526 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____10560 = (FStar_Util.fold_map (fun decls uu____10583 -> (match (uu____10583) with
| (t, uu____10597) -> begin
(

let uu____10598 = (encode_formula t env)
in (match (uu____10598) with
| (phi1, decls') -> begin
(((FStar_List.append decls decls')), (phi1))
end))
end)) [] l)
in (match (uu____10560) with
| (decls, phis) -> begin
(

let uu____10627 = (

let uu___139_10628 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___139_10628.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___139_10628.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____10627), (decls)))
end)))
in (

let eq_op = (fun r args -> (

let rf = (FStar_List.filter (fun uu____10689 -> (match (uu____10689) with
| (a, q) -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____10708)) -> begin
false
end
| uu____10709 -> begin
true
end)
end)) args)
in (match (((FStar_List.length rf) <> (Prims.parse_int "2"))) with
| true -> begin
(

let uu____10724 = (FStar_Util.format1 "eq_op: got %s non-implicit arguments instead of 2?" (Prims.string_of_int (FStar_List.length rf)))
in (failwith uu____10724))
end
| uu____10737 -> begin
(

let uu____10738 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____10738 r rf))
end)))
in (

let mk_imp1 = (fun r uu___113_10763 -> (match (uu___113_10763) with
| ((lhs, uu____10769))::((rhs, uu____10771))::[] -> begin
(

let uu____10798 = (encode_formula rhs env)
in (match (uu____10798) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____10813) -> begin
((l1), (decls1))
end
| uu____10818 -> begin
(

let uu____10819 = (encode_formula lhs env)
in (match (uu____10819) with
| (l2, decls2) -> begin
(

let uu____10830 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____10830), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____10833 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___114_10854 -> (match (uu___114_10854) with
| ((guard, uu____10860))::((_then, uu____10862))::((_else, uu____10864))::[] -> begin
(

let uu____10901 = (encode_formula guard env)
in (match (uu____10901) with
| (g, decls1) -> begin
(

let uu____10912 = (encode_formula _then env)
in (match (uu____10912) with
| (t, decls2) -> begin
(

let uu____10923 = (encode_formula _else env)
in (match (uu____10923) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____10937 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____10962 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____10962)))
in (

let connectives = (

let uu____10980 = (

let uu____10993 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Parser_Const.and_lid), (uu____10993)))
in (

let uu____11010 = (

let uu____11025 = (

let uu____11038 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Parser_Const.or_lid), (uu____11038)))
in (

let uu____11055 = (

let uu____11070 = (

let uu____11085 = (

let uu____11098 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Parser_Const.iff_lid), (uu____11098)))
in (

let uu____11115 = (

let uu____11130 = (

let uu____11145 = (

let uu____11158 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Parser_Const.not_lid), (uu____11158)))
in (uu____11145)::(((FStar_Parser_Const.eq2_lid), (eq_op)))::(((FStar_Parser_Const.eq3_lid), (eq_op)))::(((FStar_Parser_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Parser_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Parser_Const.ite_lid), (mk_ite)))::uu____11130)
in (uu____11085)::uu____11115))
in (((FStar_Parser_Const.imp_lid), (mk_imp1)))::uu____11070)
in (uu____11025)::uu____11055))
in (uu____10980)::uu____11010))
in (

let rec fallback = (fun phi1 -> (match (phi1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____11479 = (encode_formula phi' env)
in (match (uu____11479) with
| (phi2, decls) -> begin
(

let uu____11490 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi2), (msg), (r)))) r)
in ((uu____11490), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____11491) -> begin
(

let uu____11498 = (FStar_Syntax_Util.unmeta phi1)
in (encode_formula uu____11498 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____11537 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____11537) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____11549; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____11551; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____11572 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____11572) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____11619)::((x, uu____11621))::((t, uu____11623))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid) -> begin
(

let uu____11670 = (encode_term x env)
in (match (uu____11670) with
| (x1, decls) -> begin
(

let uu____11681 = (encode_term t env)
in (match (uu____11681) with
| (t1, decls') -> begin
(

let uu____11692 = (FStar_SMTEncoding_Term.mk_HasType x1 t1)
in ((uu____11692), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____11697))::((msg, uu____11699))::((phi2, uu____11701))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.labeled_lid) -> begin
(

let uu____11746 = (

let uu____11751 = (

let uu____11752 = (FStar_Syntax_Subst.compress r)
in uu____11752.FStar_Syntax_Syntax.n)
in (

let uu____11755 = (

let uu____11756 = (FStar_Syntax_Subst.compress msg)
in uu____11756.FStar_Syntax_Syntax.n)
in ((uu____11751), (uu____11755))))
in (match (uu____11746) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____11765))) -> begin
(

let phi3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi2), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r1), (false))))))) FStar_Pervasives_Native.None r1)
in (fallback phi3))
end
| uu____11775 -> begin
(fallback phi2)
end))
end
| uu____11780 when (head_redex env head2) -> begin
(

let uu____11793 = (whnf env phi1)
in (encode_formula uu____11793 env))
end
| uu____11794 -> begin
(

let uu____11807 = (encode_term phi1 env)
in (match (uu____11807) with
| (tt, decls) -> begin
(

let uu____11818 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___140_11821 = tt
in {FStar_SMTEncoding_Term.tm = uu___140_11821.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___140_11821.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____11818), (decls)))
end))
end))
end
| uu____11822 -> begin
(

let uu____11823 = (encode_term phi1 env)
in (match (uu____11823) with
| (tt, decls) -> begin
(

let uu____11834 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___141_11837 = tt
in {FStar_SMTEncoding_Term.tm = uu___141_11837.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___141_11837.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____11834), (decls)))
end))
end))
in (

let encode_q_body = (fun env1 bs ps body -> (

let uu____11873 = (encode_binders FStar_Pervasives_Native.None bs env1)
in (match (uu____11873) with
| (vars, guards, env2, decls, uu____11912) -> begin
(

let uu____11925 = (

let uu____11938 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____11986 = (

let uu____11995 = (FStar_All.pipe_right p (FStar_List.map (fun uu____12025 -> (match (uu____12025) with
| (t, uu____12035) -> begin
(encode_term t (

let uu___142_12037 = env2
in {bindings = uu___142_12037.bindings; depth = uu___142_12037.depth; tcenv = uu___142_12037.tcenv; warn = uu___142_12037.warn; cache = uu___142_12037.cache; nolabels = uu___142_12037.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___142_12037.encode_non_total_function_typ; current_module_name = uu___142_12037.current_module_name}))
end))))
in (FStar_All.pipe_right uu____11995 FStar_List.unzip))
in (match (uu____11986) with
| (p1, decls1) -> begin
((p1), ((FStar_List.flatten decls1)))
end)))))
in (FStar_All.pipe_right uu____11938 FStar_List.unzip))
in (match (uu____11925) with
| (pats, decls') -> begin
(

let uu____12136 = (encode_formula body env2)
in (match (uu____12136) with
| (body1, decls'') -> begin
(

let guards1 = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____12168; FStar_SMTEncoding_Term.rng = uu____12169})::[])::[] when ((FStar_Ident.text_of_lid FStar_Parser_Const.guard_free) = gf) -> begin
[]
end
| uu____12184 -> begin
guards
end)
in (

let uu____12189 = (FStar_SMTEncoding_Util.mk_and_l guards1)
in ((vars), (pats), (uu____12189), (body1), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug1 phi);
(

let phi1 = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____12249 -> (match (uu____12249) with
| (x, uu____12255) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats1) with
| [] -> begin
()
end
| (hd1)::tl1 -> begin
(

let pat_vars = (

let uu____12263 = (FStar_Syntax_Free.names hd1)
in (FStar_List.fold_left (fun out x -> (

let uu____12275 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____12275))) uu____12263 tl1))
in (

let uu____12278 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____12305 -> (match (uu____12305) with
| (b, uu____12311) -> begin
(

let uu____12312 = (FStar_Util.set_mem b pat_vars)
in (not (uu____12312)))
end))))
in (match (uu____12278) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____12318) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd1.FStar_Syntax_Syntax.pos tl1)
in (

let uu____12332 = (

let uu____12333 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____12333))
in (FStar_Errors.warn pos uu____12332)))
end)))
end)))
in (

let uu____12334 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____12334) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____12343 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____12401 -> (match (uu____12401) with
| (l, uu____12415) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____12343) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (uu____12448, f) -> begin
(f phi1.FStar_Syntax_Syntax.pos arms)
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____12488 = (encode_q_body env vars pats body)
in (match (uu____12488) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let tm = (

let uu____12533 = (

let uu____12544 = (FStar_SMTEncoding_Util.mkImp ((guard), (body1)))
in ((pats1), (vars1), (uu____12544)))
in (FStar_SMTEncoding_Term.mkForall uu____12533 phi1.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____12563 = (encode_q_body env vars pats body)
in (match (uu____12563) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let uu____12607 = (

let uu____12608 = (

let uu____12619 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body1)))
in ((pats1), (vars1), (uu____12619)))
in (FStar_SMTEncoding_Term.mkExists uu____12608 phi1.FStar_Syntax_Syntax.pos))
in ((uu____12607), (decls)))
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

let uu____12717 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____12717) with
| (asym, a) -> begin
(

let uu____12724 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____12724) with
| (xsym, x) -> begin
(

let uu____12731 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____12731) with
| (ysym, y) -> begin
(

let quant = (fun vars body x1 -> (

let xname_decl = (

let uu____12775 = (

let uu____12786 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in ((x1), (uu____12786), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____12775))
in (

let xtok = (Prims.strcat x1 "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let xapp = (

let uu____12812 = (

let uu____12819 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x1), (uu____12819)))
in (FStar_SMTEncoding_Util.mkApp uu____12812))
in (

let xtok1 = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok1 vars)
in (

let uu____12832 = (

let uu____12835 = (

let uu____12838 = (

let uu____12841 = (

let uu____12842 = (

let uu____12849 = (

let uu____12850 = (

let uu____12861 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____12861)))
in (FStar_SMTEncoding_Util.mkForall uu____12850))
in ((uu____12849), (FStar_Pervasives_Native.None), ((Prims.strcat "primitive_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____12842))
in (

let uu____12878 = (

let uu____12881 = (

let uu____12882 = (

let uu____12889 = (

let uu____12890 = (

let uu____12901 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____12901)))
in (FStar_SMTEncoding_Util.mkForall uu____12890))
in ((uu____12889), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____12882))
in (uu____12881)::[])
in (uu____12841)::uu____12878))
in (xtok_decl)::uu____12838)
in (xname_decl)::uu____12835)
in ((xtok1), (uu____12832))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims1 = (

let uu____12992 = (

let uu____13005 = (

let uu____13014 = (

let uu____13015 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13015))
in (quant axy uu____13014))
in ((FStar_Parser_Const.op_Eq), (uu____13005)))
in (

let uu____13024 = (

let uu____13039 = (

let uu____13052 = (

let uu____13061 = (

let uu____13062 = (

let uu____13063 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____13063))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13062))
in (quant axy uu____13061))
in ((FStar_Parser_Const.op_notEq), (uu____13052)))
in (

let uu____13072 = (

let uu____13087 = (

let uu____13100 = (

let uu____13109 = (

let uu____13110 = (

let uu____13111 = (

let uu____13116 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13117 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13116), (uu____13117))))
in (FStar_SMTEncoding_Util.mkLT uu____13111))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13110))
in (quant xy uu____13109))
in ((FStar_Parser_Const.op_LT), (uu____13100)))
in (

let uu____13126 = (

let uu____13141 = (

let uu____13154 = (

let uu____13163 = (

let uu____13164 = (

let uu____13165 = (

let uu____13170 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13171 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13170), (uu____13171))))
in (FStar_SMTEncoding_Util.mkLTE uu____13165))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13164))
in (quant xy uu____13163))
in ((FStar_Parser_Const.op_LTE), (uu____13154)))
in (

let uu____13180 = (

let uu____13195 = (

let uu____13208 = (

let uu____13217 = (

let uu____13218 = (

let uu____13219 = (

let uu____13224 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13225 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13224), (uu____13225))))
in (FStar_SMTEncoding_Util.mkGT uu____13219))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13218))
in (quant xy uu____13217))
in ((FStar_Parser_Const.op_GT), (uu____13208)))
in (

let uu____13234 = (

let uu____13249 = (

let uu____13262 = (

let uu____13271 = (

let uu____13272 = (

let uu____13273 = (

let uu____13278 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13279 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13278), (uu____13279))))
in (FStar_SMTEncoding_Util.mkGTE uu____13273))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13272))
in (quant xy uu____13271))
in ((FStar_Parser_Const.op_GTE), (uu____13262)))
in (

let uu____13288 = (

let uu____13303 = (

let uu____13316 = (

let uu____13325 = (

let uu____13326 = (

let uu____13327 = (

let uu____13332 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13333 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13332), (uu____13333))))
in (FStar_SMTEncoding_Util.mkSub uu____13327))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13326))
in (quant xy uu____13325))
in ((FStar_Parser_Const.op_Subtraction), (uu____13316)))
in (

let uu____13342 = (

let uu____13357 = (

let uu____13370 = (

let uu____13379 = (

let uu____13380 = (

let uu____13381 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____13381))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13380))
in (quant qx uu____13379))
in ((FStar_Parser_Const.op_Minus), (uu____13370)))
in (

let uu____13390 = (

let uu____13405 = (

let uu____13418 = (

let uu____13427 = (

let uu____13428 = (

let uu____13429 = (

let uu____13434 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13435 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13434), (uu____13435))))
in (FStar_SMTEncoding_Util.mkAdd uu____13429))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13428))
in (quant xy uu____13427))
in ((FStar_Parser_Const.op_Addition), (uu____13418)))
in (

let uu____13444 = (

let uu____13459 = (

let uu____13472 = (

let uu____13481 = (

let uu____13482 = (

let uu____13483 = (

let uu____13488 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13489 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13488), (uu____13489))))
in (FStar_SMTEncoding_Util.mkMul uu____13483))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13482))
in (quant xy uu____13481))
in ((FStar_Parser_Const.op_Multiply), (uu____13472)))
in (

let uu____13498 = (

let uu____13513 = (

let uu____13526 = (

let uu____13535 = (

let uu____13536 = (

let uu____13537 = (

let uu____13542 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13543 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13542), (uu____13543))))
in (FStar_SMTEncoding_Util.mkDiv uu____13537))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13536))
in (quant xy uu____13535))
in ((FStar_Parser_Const.op_Division), (uu____13526)))
in (

let uu____13552 = (

let uu____13567 = (

let uu____13580 = (

let uu____13589 = (

let uu____13590 = (

let uu____13591 = (

let uu____13596 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13597 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13596), (uu____13597))))
in (FStar_SMTEncoding_Util.mkMod uu____13591))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13590))
in (quant xy uu____13589))
in ((FStar_Parser_Const.op_Modulus), (uu____13580)))
in (

let uu____13606 = (

let uu____13621 = (

let uu____13634 = (

let uu____13643 = (

let uu____13644 = (

let uu____13645 = (

let uu____13650 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____13651 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____13650), (uu____13651))))
in (FStar_SMTEncoding_Util.mkAnd uu____13645))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13644))
in (quant xy uu____13643))
in ((FStar_Parser_Const.op_And), (uu____13634)))
in (

let uu____13660 = (

let uu____13675 = (

let uu____13688 = (

let uu____13697 = (

let uu____13698 = (

let uu____13699 = (

let uu____13704 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____13705 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____13704), (uu____13705))))
in (FStar_SMTEncoding_Util.mkOr uu____13699))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13698))
in (quant xy uu____13697))
in ((FStar_Parser_Const.op_Or), (uu____13688)))
in (

let uu____13714 = (

let uu____13729 = (

let uu____13742 = (

let uu____13751 = (

let uu____13752 = (

let uu____13753 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____13753))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13752))
in (quant qx uu____13751))
in ((FStar_Parser_Const.op_Negation), (uu____13742)))
in (uu____13729)::[])
in (uu____13675)::uu____13714))
in (uu____13621)::uu____13660))
in (uu____13567)::uu____13606))
in (uu____13513)::uu____13552))
in (uu____13459)::uu____13498))
in (uu____13405)::uu____13444))
in (uu____13357)::uu____13390))
in (uu____13303)::uu____13342))
in (uu____13249)::uu____13288))
in (uu____13195)::uu____13234))
in (uu____13141)::uu____13180))
in (uu____13087)::uu____13126))
in (uu____13039)::uu____13072))
in (uu____12992)::uu____13024))
in (

let mk1 = (fun l v1 -> (

let uu____13967 = (

let uu____13976 = (FStar_All.pipe_right prims1 (FStar_List.find (fun uu____14034 -> (match (uu____14034) with
| (l', uu____14048) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____13976 (FStar_Option.map (fun uu____14108 -> (match (uu____14108) with
| (uu____14127, b) -> begin
(b v1)
end)))))
in (FStar_All.pipe_right uu____13967 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims1 (FStar_Util.for_some (fun uu____14198 -> (match (uu____14198) with
| (l', uu____14212) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk1; is = is})))))))
end))
end))
end))


let pretype_axiom : env_t  ->  FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun env tapp vars -> (

let uu____14253 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____14253) with
| (xxsym, xx) -> begin
(

let uu____14260 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____14260) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let module_name = env.current_module_name
in (

let uu____14270 = (

let uu____14277 = (

let uu____14278 = (

let uu____14289 = (

let uu____14290 = (

let uu____14295 = (

let uu____14296 = (

let uu____14301 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____14301)))
in (FStar_SMTEncoding_Util.mkEq uu____14296))
in ((xx_has_type), (uu____14295)))
in (FStar_SMTEncoding_Util.mkImp uu____14290))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____14289)))
in (FStar_SMTEncoding_Util.mkForall uu____14278))
in (

let uu____14326 = (

let uu____14327 = (

let uu____14328 = (

let uu____14329 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "_pretyping_" uu____14329))
in (Prims.strcat module_name uu____14328))
in (varops.mk_unique uu____14327))
in ((uu____14277), (FStar_Pervasives_Native.Some ("pretyping")), (uu____14326))))
in (FStar_SMTEncoding_Util.mkAssume uu____14270)))))
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

let uu____14369 = (

let uu____14370 = (

let uu____14377 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____14377), (FStar_Pervasives_Native.Some ("unit typing")), ("unit_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____14370))
in (

let uu____14380 = (

let uu____14383 = (

let uu____14384 = (

let uu____14391 = (

let uu____14392 = (

let uu____14403 = (

let uu____14404 = (

let uu____14409 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____14409)))
in (FStar_SMTEncoding_Util.mkImp uu____14404))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____14403)))
in (mkForall_fuel uu____14392))
in ((uu____14391), (FStar_Pervasives_Native.Some ("unit inversion")), ("unit_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____14384))
in (uu____14383)::[])
in (uu____14369)::uu____14380))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____14451 = (

let uu____14452 = (

let uu____14459 = (

let uu____14460 = (

let uu____14471 = (

let uu____14476 = (

let uu____14479 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____14479)::[])
in (uu____14476)::[])
in (

let uu____14484 = (

let uu____14485 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____14485 tt))
in ((uu____14471), ((bb)::[]), (uu____14484))))
in (FStar_SMTEncoding_Util.mkForall uu____14460))
in ((uu____14459), (FStar_Pervasives_Native.Some ("bool typing")), ("bool_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____14452))
in (

let uu____14506 = (

let uu____14509 = (

let uu____14510 = (

let uu____14517 = (

let uu____14518 = (

let uu____14529 = (

let uu____14530 = (

let uu____14535 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxBoolFun) x)
in ((typing_pred), (uu____14535)))
in (FStar_SMTEncoding_Util.mkImp uu____14530))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____14529)))
in (mkForall_fuel uu____14518))
in ((uu____14517), (FStar_Pervasives_Native.Some ("bool inversion")), ("bool_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____14510))
in (uu____14509)::[])
in (uu____14451)::uu____14506))))))
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

let uu____14585 = (

let uu____14586 = (

let uu____14593 = (

let uu____14596 = (

let uu____14599 = (

let uu____14602 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____14603 = (

let uu____14606 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____14606)::[])
in (uu____14602)::uu____14603))
in (tt)::uu____14599)
in (tt)::uu____14596)
in (("Prims.Precedes"), (uu____14593)))
in (FStar_SMTEncoding_Util.mkApp uu____14586))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14585))
in (

let precedes_y_x = (

let uu____14610 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14610))
in (

let uu____14613 = (

let uu____14614 = (

let uu____14621 = (

let uu____14622 = (

let uu____14633 = (

let uu____14638 = (

let uu____14641 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____14641)::[])
in (uu____14638)::[])
in (

let uu____14646 = (

let uu____14647 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____14647 tt))
in ((uu____14633), ((bb)::[]), (uu____14646))))
in (FStar_SMTEncoding_Util.mkForall uu____14622))
in ((uu____14621), (FStar_Pervasives_Native.Some ("int typing")), ("int_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____14614))
in (

let uu____14668 = (

let uu____14671 = (

let uu____14672 = (

let uu____14679 = (

let uu____14680 = (

let uu____14691 = (

let uu____14692 = (

let uu____14697 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxIntFun) x)
in ((typing_pred), (uu____14697)))
in (FStar_SMTEncoding_Util.mkImp uu____14692))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____14691)))
in (mkForall_fuel uu____14680))
in ((uu____14679), (FStar_Pervasives_Native.Some ("int inversion")), ("int_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____14672))
in (

let uu____14722 = (

let uu____14725 = (

let uu____14726 = (

let uu____14733 = (

let uu____14734 = (

let uu____14745 = (

let uu____14746 = (

let uu____14751 = (

let uu____14752 = (

let uu____14755 = (

let uu____14758 = (

let uu____14761 = (

let uu____14762 = (

let uu____14767 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14768 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____14767), (uu____14768))))
in (FStar_SMTEncoding_Util.mkGT uu____14762))
in (

let uu____14769 = (

let uu____14772 = (

let uu____14773 = (

let uu____14778 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____14779 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____14778), (uu____14779))))
in (FStar_SMTEncoding_Util.mkGTE uu____14773))
in (

let uu____14780 = (

let uu____14783 = (

let uu____14784 = (

let uu____14789 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____14790 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____14789), (uu____14790))))
in (FStar_SMTEncoding_Util.mkLT uu____14784))
in (uu____14783)::[])
in (uu____14772)::uu____14780))
in (uu____14761)::uu____14769))
in (typing_pred_y)::uu____14758)
in (typing_pred)::uu____14755)
in (FStar_SMTEncoding_Util.mk_and_l uu____14752))
in ((uu____14751), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____14746))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____14745)))
in (mkForall_fuel uu____14734))
in ((uu____14733), (FStar_Pervasives_Native.Some ("well-founded ordering on nat (alt)")), ("well-founded-ordering-on-nat")))
in (FStar_SMTEncoding_Util.mkAssume uu____14726))
in (uu____14725)::[])
in (uu____14671)::uu____14722))
in (uu____14613)::uu____14668)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____14836 = (

let uu____14837 = (

let uu____14844 = (

let uu____14845 = (

let uu____14856 = (

let uu____14861 = (

let uu____14864 = (FStar_SMTEncoding_Term.boxString b)
in (uu____14864)::[])
in (uu____14861)::[])
in (

let uu____14869 = (

let uu____14870 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____14870 tt))
in ((uu____14856), ((bb)::[]), (uu____14869))))
in (FStar_SMTEncoding_Util.mkForall uu____14845))
in ((uu____14844), (FStar_Pervasives_Native.Some ("string typing")), ("string_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____14837))
in (

let uu____14891 = (

let uu____14894 = (

let uu____14895 = (

let uu____14902 = (

let uu____14903 = (

let uu____14914 = (

let uu____14915 = (

let uu____14920 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxStringFun) x)
in ((typing_pred), (uu____14920)))
in (FStar_SMTEncoding_Util.mkImp uu____14915))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____14914)))
in (mkForall_fuel uu____14903))
in ((uu____14902), (FStar_Pervasives_Native.Some ("string inversion")), ("string_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____14895))
in (uu____14894)::[])
in (uu____14836)::uu____14891))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in ((FStar_SMTEncoding_Util.mkAssume ((valid), (FStar_Pervasives_Native.Some ("True interpretation")), ("true_interp"))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____14973 = (

let uu____14974 = (

let uu____14981 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____14981), (FStar_Pervasives_Native.Some ("False interpretation")), ("false_interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____14974))
in (uu____14973)::[])))
in (

let mk_and_interp = (fun env conj uu____14993 -> (

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

let uu____15018 = (

let uu____15019 = (

let uu____15026 = (

let uu____15027 = (

let uu____15038 = (

let uu____15039 = (

let uu____15044 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____15044), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15039))
in ((((l_and_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15038)))
in (FStar_SMTEncoding_Util.mkForall uu____15027))
in ((uu____15026), (FStar_Pervasives_Native.Some ("/\\ interpretation")), ("l_and-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15019))
in (uu____15018)::[]))))))))))
in (

let mk_or_interp = (fun env disj uu____15082 -> (

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

let uu____15107 = (

let uu____15108 = (

let uu____15115 = (

let uu____15116 = (

let uu____15127 = (

let uu____15128 = (

let uu____15133 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____15133), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15128))
in ((((l_or_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15127)))
in (FStar_SMTEncoding_Util.mkForall uu____15116))
in ((uu____15115), (FStar_Pervasives_Native.Some ("\\/ interpretation")), ("l_or-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15108))
in (uu____15107)::[]))))))))))
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

let uu____15196 = (

let uu____15197 = (

let uu____15204 = (

let uu____15205 = (

let uu____15216 = (

let uu____15217 = (

let uu____15222 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____15222), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15217))
in ((((eq2_x_y)::[])::[]), ((aa)::(xx1)::(yy1)::[]), (uu____15216)))
in (FStar_SMTEncoding_Util.mkForall uu____15205))
in ((uu____15204), (FStar_Pervasives_Native.Some ("Eq2 interpretation")), ("eq2-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15197))
in (uu____15196)::[]))))))))))
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

let uu____15295 = (

let uu____15296 = (

let uu____15303 = (

let uu____15304 = (

let uu____15315 = (

let uu____15316 = (

let uu____15321 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____15321), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15316))
in ((((eq3_x_y)::[])::[]), ((aa)::(bb)::(xx1)::(yy1)::[]), (uu____15315)))
in (FStar_SMTEncoding_Util.mkForall uu____15304))
in ((uu____15303), (FStar_Pervasives_Native.Some ("Eq3 interpretation")), ("eq3-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15296))
in (uu____15295)::[]))))))))))))
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

let uu____15392 = (

let uu____15393 = (

let uu____15400 = (

let uu____15401 = (

let uu____15412 = (

let uu____15413 = (

let uu____15418 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____15418), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15413))
in ((((l_imp_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15412)))
in (FStar_SMTEncoding_Util.mkForall uu____15401))
in ((uu____15400), (FStar_Pervasives_Native.Some ("==> interpretation")), ("l_imp-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15393))
in (uu____15392)::[]))))))))))
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

let uu____15481 = (

let uu____15482 = (

let uu____15489 = (

let uu____15490 = (

let uu____15501 = (

let uu____15502 = (

let uu____15507 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____15507), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15502))
in ((((l_iff_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15501)))
in (FStar_SMTEncoding_Util.mkForall uu____15490))
in ((uu____15489), (FStar_Pervasives_Native.Some ("<==> interpretation")), ("l_iff-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15482))
in (uu____15481)::[]))))))))))
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

let uu____15559 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15559))
in (

let uu____15562 = (

let uu____15563 = (

let uu____15570 = (

let uu____15571 = (

let uu____15582 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((l_not_a)::[])::[]), ((aa)::[]), (uu____15582)))
in (FStar_SMTEncoding_Util.mkForall uu____15571))
in ((uu____15570), (FStar_Pervasives_Native.Some ("not interpretation")), ("l_not-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15563))
in (uu____15562)::[])))))))
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

let uu____15642 = (

let uu____15649 = (

let uu____15652 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____15652)::[])
in (("Valid"), (uu____15649)))
in (FStar_SMTEncoding_Util.mkApp uu____15642))
in (

let uu____15655 = (

let uu____15656 = (

let uu____15663 = (

let uu____15664 = (

let uu____15675 = (

let uu____15676 = (

let uu____15681 = (

let uu____15682 = (

let uu____15693 = (

let uu____15698 = (

let uu____15701 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____15701)::[])
in (uu____15698)::[])
in (

let uu____15706 = (

let uu____15707 = (

let uu____15712 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____15712), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____15707))
in ((uu____15693), ((xx1)::[]), (uu____15706))))
in (FStar_SMTEncoding_Util.mkForall uu____15682))
in ((uu____15681), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15676))
in ((((l_forall_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15675)))
in (FStar_SMTEncoding_Util.mkForall uu____15664))
in ((uu____15663), (FStar_Pervasives_Native.Some ("forall interpretation")), ("forall-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15656))
in (uu____15655)::[])))))))))))
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

let uu____15794 = (

let uu____15801 = (

let uu____15804 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____15804)::[])
in (("Valid"), (uu____15801)))
in (FStar_SMTEncoding_Util.mkApp uu____15794))
in (

let uu____15807 = (

let uu____15808 = (

let uu____15815 = (

let uu____15816 = (

let uu____15827 = (

let uu____15828 = (

let uu____15833 = (

let uu____15834 = (

let uu____15845 = (

let uu____15850 = (

let uu____15853 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____15853)::[])
in (uu____15850)::[])
in (

let uu____15858 = (

let uu____15859 = (

let uu____15864 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____15864), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____15859))
in ((uu____15845), ((xx1)::[]), (uu____15858))))
in (FStar_SMTEncoding_Util.mkExists uu____15834))
in ((uu____15833), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15828))
in ((((l_exists_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15827)))
in (FStar_SMTEncoding_Util.mkForall uu____15816))
in ((uu____15815), (FStar_Pervasives_Native.Some ("exists interpretation")), ("exists-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15808))
in (uu____15807)::[])))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____15924 = (

let uu____15925 = (

let uu____15932 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (

let uu____15933 = (varops.mk_unique "typing_range_const")
in ((uu____15932), (FStar_Pervasives_Native.Some ("Range_const typing")), (uu____15933))))
in (FStar_SMTEncoding_Util.mkAssume uu____15925))
in (uu____15924)::[])))
in (

let prims1 = (((FStar_Parser_Const.unit_lid), (mk_unit)))::(((FStar_Parser_Const.bool_lid), (mk_bool)))::(((FStar_Parser_Const.int_lid), (mk_int)))::(((FStar_Parser_Const.string_lid), (mk_str)))::(((FStar_Parser_Const.true_lid), (mk_true_interp)))::(((FStar_Parser_Const.false_lid), (mk_false_interp)))::(((FStar_Parser_Const.and_lid), (mk_and_interp)))::(((FStar_Parser_Const.or_lid), (mk_or_interp)))::(((FStar_Parser_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Parser_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Parser_Const.imp_lid), (mk_imp_interp)))::(((FStar_Parser_Const.iff_lid), (mk_iff_interp)))::(((FStar_Parser_Const.not_lid), (mk_not_interp)))::(((FStar_Parser_Const.forall_lid), (mk_forall_interp)))::(((FStar_Parser_Const.exists_lid), (mk_exists_interp)))::(((FStar_Parser_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (

let uu____16219 = (FStar_Util.find_opt (fun uu____16245 -> (match (uu____16245) with
| (l, uu____16257) -> begin
(FStar_Ident.lid_equals l t)
end)) prims1)
in (match (uu____16219) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____16282, f) -> begin
(f env s tt)
end))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____16321 = (encode_function_type_as_formula t env)
in (match (uu____16321) with
| (form, decls) -> begin
(FStar_List.append decls (((FStar_SMTEncoding_Util.mkAssume ((form), (FStar_Pervasives_Native.Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____16363 = ((

let uu____16366 = ((FStar_Syntax_Util.is_pure_or_ghost_function t_norm) || (FStar_TypeChecker_Env.is_reifiable_function env.tcenv t_norm))
in (FStar_All.pipe_left Prims.op_Negation uu____16366)) || (FStar_Syntax_Util.is_lemma t_norm))
in (match (uu____16363) with
| true -> begin
(

let uu____16373 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____16373) with
| (vname, vtok, env1) -> begin
(

let arg_sorts = (

let uu____16392 = (

let uu____16393 = (FStar_Syntax_Subst.compress t_norm)
in uu____16393.FStar_Syntax_Syntax.n)
in (match (uu____16392) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____16399) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____16429 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____16434 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env1)))))
end))
end
| uu____16447 -> begin
(

let uu____16448 = (prims.is lid)
in (match (uu____16448) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____16456 = (prims.mk lid vname)
in (match (uu____16456) with
| (tok, definition) -> begin
(

let env1 = (push_free_var env lid vname (FStar_Pervasives_Native.Some (tok)))
in ((definition), (env1)))
end)))
end
| uu____16478 -> begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let uu____16480 = (

let uu____16491 = (curried_arrow_formals_comp t_norm)
in (match (uu____16491) with
| (args, comp) -> begin
(

let comp1 = (

let uu____16509 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv comp)
in (match (uu____16509) with
| true -> begin
(

let uu____16510 = (FStar_TypeChecker_Env.reify_comp (

let uu___143_16513 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___143_16513.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___143_16513.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___143_16513.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___143_16513.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___143_16513.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___143_16513.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___143_16513.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___143_16513.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___143_16513.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___143_16513.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___143_16513.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___143_16513.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___143_16513.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___143_16513.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___143_16513.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___143_16513.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___143_16513.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___143_16513.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___143_16513.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___143_16513.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___143_16513.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___143_16513.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___143_16513.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___143_16513.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___143_16513.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___143_16513.FStar_TypeChecker_Env.is_native_tactic}) comp FStar_Syntax_Syntax.U_unknown)
in (FStar_Syntax_Syntax.mk_Total uu____16510))
end
| uu____16514 -> begin
comp
end))
in (match (encode_non_total_function_typ) with
| true -> begin
(

let uu____16525 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp1)
in ((args), (uu____16525)))
end
| uu____16538 -> begin
((args), (((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp1)))))
end))
end))
in (match (uu____16480) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____16570 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____16570) with
| (vname, vtok, env1) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____16591 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___115_16633 -> (match (uu___115_16633) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____16637 = (FStar_Util.prefix vars)
in (match (uu____16637) with
| (uu____16658, (xxsym, uu____16660)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____16678 = (

let uu____16679 = (

let uu____16686 = (

let uu____16687 = (

let uu____16698 = (

let uu____16699 = (

let uu____16704 = (

let uu____16705 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____16705))
in ((vapp), (uu____16704)))
in (FStar_SMTEncoding_Util.mkEq uu____16699))
in ((((vapp)::[])::[]), (vars), (uu____16698)))
in (FStar_SMTEncoding_Util.mkForall uu____16687))
in ((uu____16686), (FStar_Pervasives_Native.Some ("Discriminator equation")), ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))
in (FStar_SMTEncoding_Util.mkAssume uu____16679))
in (uu____16678)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____16724 = (FStar_Util.prefix vars)
in (match (uu____16724) with
| (uu____16745, (xxsym, uu____16747)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f1 = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f1)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____16770 = (

let uu____16771 = (

let uu____16778 = (

let uu____16779 = (

let uu____16790 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____16790)))
in (FStar_SMTEncoding_Util.mkForall uu____16779))
in ((uu____16778), (FStar_Pervasives_Native.Some ("Projector equation")), ((Prims.strcat "proj_equation_" tp_name))))
in (FStar_SMTEncoding_Util.mkAssume uu____16771))
in (uu____16770)::[])))))
end))
end
| uu____16807 -> begin
[]
end)))))
in (

let uu____16808 = (encode_binders FStar_Pervasives_Native.None formals env1)
in (match (uu____16808) with
| (vars, guards, env', decls1, uu____16835) -> begin
(

let uu____16848 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____16857 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____16857), (decls1)))
end
| FStar_Pervasives_Native.Some (p) -> begin
(

let uu____16859 = (encode_formula p env')
in (match (uu____16859) with
| (g, ds) -> begin
(

let uu____16870 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____16870), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____16848) with
| (guard, decls11) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____16883 = (

let uu____16890 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____16890)))
in (FStar_SMTEncoding_Util.mkApp uu____16883))
in (

let uu____16899 = (

let vname_decl = (

let uu____16907 = (

let uu____16918 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____16928 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____16918), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____16907))
in (

let uu____16937 = (

let env2 = (

let uu___144_16943 = env1
in {bindings = uu___144_16943.bindings; depth = uu___144_16943.depth; tcenv = uu___144_16943.tcenv; warn = uu___144_16943.warn; cache = uu___144_16943.cache; nolabels = uu___144_16943.nolabels; use_zfuel_name = uu___144_16943.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = uu___144_16943.current_module_name})
in (

let uu____16944 = (

let uu____16945 = (head_normal env2 tt)
in (not (uu____16945)))
in (match (uu____16944) with
| true -> begin
(encode_term_pred FStar_Pervasives_Native.None tt env2 vtok_tm)
end
| uu____16950 -> begin
(encode_term_pred FStar_Pervasives_Native.None t_norm env2 vtok_tm)
end)))
in (match (uu____16937) with
| (tok_typing, decls2) -> begin
(

let tok_typing1 = (match (formals) with
| (uu____16960)::uu____16961 -> begin
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

let uu____17001 = (

let uu____17012 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____17012)))
in (FStar_SMTEncoding_Util.mkForall uu____17001))
in (FStar_SMTEncoding_Util.mkAssume ((guarded_tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname)))))))))
end
| uu____17039 -> begin
(FStar_SMTEncoding_Util.mkAssume ((tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname))))
end)
in (

let uu____17042 = (match (formals) with
| [] -> begin
(

let uu____17059 = (

let uu____17060 = (

let uu____17063 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)) uu____17063))
in (push_free_var env1 lid vname uu____17060))
in (((FStar_List.append decls2 ((tok_typing1)::[]))), (uu____17059)))
end
| uu____17068 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let vtok_fresh = (

let uu____17075 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) uu____17075))
in (

let name_tok_corr = (

let uu____17077 = (

let uu____17084 = (

let uu____17085 = (

let uu____17096 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____17096)))
in (FStar_SMTEncoding_Util.mkForall uu____17085))
in ((uu____17084), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____17077))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing1)::[]))), (env1)))))
end)
in (match (uu____17042) with
| (tok_decl, env2) -> begin
(((vname_decl)::tok_decl), (env2))
end)))
end)))
in (match (uu____16899) with
| (decls2, env2) -> begin
(

let uu____17139 = (

let res_t1 = (FStar_Syntax_Subst.compress res_t)
in (

let uu____17147 = (encode_term res_t1 env')
in (match (uu____17147) with
| (encoded_res_t, decls) -> begin
(

let uu____17160 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____17160), (decls)))
end)))
in (match (uu____17139) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____17171 = (

let uu____17178 = (

let uu____17179 = (

let uu____17190 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____17190)))
in (FStar_SMTEncoding_Util.mkForall uu____17179))
in ((uu____17178), (FStar_Pervasives_Native.Some ("free var typing")), ((Prims.strcat "typing_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____17171))
in (

let freshness = (

let uu____17206 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____17206) with
| true -> begin
(

let uu____17211 = (

let uu____17212 = (

let uu____17223 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in (

let uu____17234 = (varops.next_id ())
in ((vname), (uu____17223), (FStar_SMTEncoding_Term.Term_sort), (uu____17234))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____17212))
in (

let uu____17237 = (

let uu____17240 = (pretype_axiom env2 vapp vars)
in (uu____17240)::[])
in (uu____17211)::uu____17237))
end
| uu____17241 -> begin
[]
end))
in (

let g = (

let uu____17245 = (

let uu____17248 = (

let uu____17251 = (

let uu____17254 = (

let uu____17257 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____17257)
in (FStar_List.append freshness uu____17254))
in (FStar_List.append decls3 uu____17251))
in (FStar_List.append decls2 uu____17248))
in (FStar_List.append decls11 uu____17245))
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

let uu____17292 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17292) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17329 = (encode_free_var env x t t_norm [])
in (match (uu____17329) with
| (decls, env1) -> begin
(

let uu____17356 = (lookup_lid env1 x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____17356) with
| (n1, x', uu____17383) -> begin
((((n1), (x'))), (decls), (env1))
end))
end))
end
| FStar_Pervasives_Native.Some (n1, x1, uu____17404) -> begin
((((n1), (x1))), ([]), (env))
end)))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let uu____17460 = (encode_free_var env lid t tt quals)
in (match (uu____17460) with
| (decls, env1) -> begin
(

let uu____17479 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____17479) with
| true -> begin
(

let uu____17486 = (

let uu____17489 = (encode_smt_lemma env1 lid tt)
in (FStar_List.append decls uu____17489))
in ((uu____17486), (env1)))
end
| uu____17494 -> begin
((decls), (env1))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____17544 lb -> (match (uu____17544) with
| (decls, env1) -> begin
(

let uu____17564 = (

let uu____17571 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env1 uu____17571 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____17564) with
| (decls', env2) -> begin
(((FStar_List.append decls decls')), (env2))
end))
end)) (([]), (env)))))


let is_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let fstar_tactics_tactic_lid = (FStar_Parser_Const.p2l (("FStar")::("Tactics")::("tactic")::[]))
in (

let uu____17593 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____17593) with
| (hd1, args) -> begin
(

let uu____17630 = (

let uu____17631 = (FStar_Syntax_Util.un_uinst hd1)
in uu____17631.FStar_Syntax_Syntax.n)
in (match (uu____17630) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____17635, c) -> begin
(

let effect_name = (FStar_Syntax_Util.comp_effect_name c)
in (FStar_Util.starts_with "FStar.Tactics" effect_name.FStar_Ident.str))
end
| uu____17654 -> begin
false
end))
end))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____17679 quals -> (match (uu____17679) with
| (is_rec, bindings) -> begin
(

let eta_expand1 = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____17755 = (FStar_Util.first_N nbinders formals)
in (match (uu____17755) with
| (formals1, extra_formals) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____17836 uu____17837 -> (match (((uu____17836), (uu____17837))) with
| ((formal, uu____17855), (binder, uu____17857)) -> begin
(

let uu____17866 = (

let uu____17873 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____17873)))
in FStar_Syntax_Syntax.NT (uu____17866))
end)) formals1 binders)
in (

let extra_formals1 = (

let uu____17881 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____17912 -> (match (uu____17912) with
| (x, i) -> begin
(

let uu____17923 = (

let uu___145_17924 = x
in (

let uu____17925 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___145_17924.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___145_17924.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____17925}))
in ((uu____17923), (i)))
end))))
in (FStar_All.pipe_right uu____17881 FStar_Syntax_Util.name_binders))
in (

let body1 = (

let uu____17943 = (

let uu____17944 = (FStar_Syntax_Subst.compress body)
in (

let uu____17945 = (

let uu____17946 = (FStar_Syntax_Util.args_of_binders extra_formals1)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____17946))
in (FStar_Syntax_Syntax.extend_app_n uu____17944 uu____17945)))
in (uu____17943 FStar_Pervasives_Native.None body.FStar_Syntax_Syntax.pos))
in (((FStar_List.append binders extra_formals1)), (body1)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let get_result_type = (fun c -> (

let uu____18007 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c)
in (match (uu____18007) with
| true -> begin
(FStar_TypeChecker_Env.reify_comp (

let uu___146_18010 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___146_18010.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___146_18010.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___146_18010.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___146_18010.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___146_18010.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___146_18010.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___146_18010.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___146_18010.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___146_18010.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___146_18010.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___146_18010.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___146_18010.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___146_18010.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___146_18010.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___146_18010.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___146_18010.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___146_18010.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___146_18010.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___146_18010.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___146_18010.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___146_18010.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___146_18010.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___146_18010.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___146_18010.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___146_18010.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___146_18010.FStar_TypeChecker_Env.is_native_tactic}) c FStar_Syntax_Syntax.U_unknown)
end
| uu____18011 -> begin
(FStar_Syntax_Util.comp_result c)
end)))
in (

let rec aux = (fun norm1 t_norm1 -> (

let uu____18043 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____18043) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____18107)::uu____18108 -> begin
(

let uu____18123 = (

let uu____18124 = (FStar_Syntax_Subst.compress t_norm1)
in uu____18124.FStar_Syntax_Syntax.n)
in (match (uu____18123) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____18169 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____18169) with
| (formals1, c1) -> begin
(

let nformals = (FStar_List.length formals1)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (get_result_type c1)
in (

let uu____18211 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c1))
in (match (uu____18211) with
| true -> begin
(

let uu____18246 = (FStar_Util.first_N nformals binders)
in (match (uu____18246) with
| (bs0, rest) -> begin
(

let c2 = (

let subst1 = (FStar_List.map2 (fun uu____18340 uu____18341 -> (match (((uu____18340), (uu____18341))) with
| ((x, uu____18359), (b, uu____18361)) -> begin
(

let uu____18370 = (

let uu____18377 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____18377)))
in FStar_Syntax_Syntax.NT (uu____18370))
end)) formals1 bs0)
in (FStar_Syntax_Subst.subst_comp subst1 c1))
in (

let body1 = (FStar_Syntax_Util.abs rest body lopt)
in (

let uu____18379 = (

let uu____18400 = (get_result_type c2)
in ((bs0), (body1), (bs0), (uu____18400)))
in ((uu____18379), (false)))))
end))
end
| uu____18433 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____18468 = (eta_expand1 binders formals1 body tres)
in (match (uu____18468) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end))
end
| uu____18547 -> begin
((((binders), (body), (formals1), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____18557) -> begin
(

let uu____18562 = (

let uu____18583 = (aux norm1 x.FStar_Syntax_Syntax.sort)
in (FStar_Pervasives_Native.fst uu____18583))
in ((uu____18562), (true)))
end
| uu____18648 when (not (norm1)) -> begin
(

let t_norm2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm1)
in (aux true t_norm2))
end
| uu____18650 -> begin
(

let uu____18651 = (

let uu____18652 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____18653 = (FStar_Syntax_Print.term_to_string t_norm1)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____18652 uu____18653)))
in (failwith uu____18651))
end))
end
| uu____18678 -> begin
(

let uu____18679 = (

let uu____18680 = (FStar_Syntax_Subst.compress t_norm1)
in uu____18680.FStar_Syntax_Syntax.n)
in (match (uu____18679) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____18725 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____18725) with
| (formals1, c1) -> begin
(

let tres = (get_result_type c1)
in (

let uu____18757 = (eta_expand1 [] formals1 e tres)
in (match (uu____18757) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end)))
end))
end
| uu____18840 -> begin
(((([]), (e), ([]), (t_norm1))), (false))
end))
end)
end)))
in (aux false t_norm))))
in try
(match (()) with
| () -> begin
(

let uu____18896 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> ((FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))))
in (match (uu____18896) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____18907 -> begin
(

let uu____18908 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____19002 lb -> (match (uu____19002) with
| (toks, typs, decls, env1) -> begin
((

let uu____19097 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____19097) with
| true -> begin
(FStar_Pervasives.raise Let_rec_unencodeable)
end
| uu____19098 -> begin
()
end));
(

let t_norm = (whnf env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____19100 = (

let uu____19115 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env1 uu____19115 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____19100) with
| (tok, decl, env2) -> begin
(

let uu____19161 = (

let uu____19174 = (

let uu____19185 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((uu____19185), (tok)))
in (uu____19174)::toks)
in ((uu____19161), ((t_norm)::typs), ((decl)::decls), (env2)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____18908) with
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
| uu____19368 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| FStar_Pervasives_Native.Some (ftok1) -> begin
(mk_Apply ftok1 vars)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____19376 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____19376 vars))
end)
end
| uu____19377 -> begin
(

let uu____19378 = (

let uu____19385 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____19385)))
in (FStar_SMTEncoding_Util.mkApp uu____19378))
end)
end))
in (

let uu____19394 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___116_19398 -> (match (uu___116_19398) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____19399 -> begin
false
end)))) || (FStar_All.pipe_right typs1 (FStar_Util.for_some (fun t -> (

let uu____19405 = ((FStar_Syntax_Util.is_pure_or_ghost_function t) || (FStar_TypeChecker_Env.is_reifiable_function env1.tcenv t))
in (FStar_All.pipe_left Prims.op_Negation uu____19405))))))
in (match (uu____19394) with
| true -> begin
((decls1), (env1))
end
| uu____19414 -> begin
(match ((not (is_rec))) with
| true -> begin
(match (((bindings), (typs1), (toks1))) with
| (({FStar_Syntax_Syntax.lbname = uu____19443; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____19445; FStar_Syntax_Syntax.lbeff = uu____19446; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____19509 = (

let uu____19516 = (FStar_TypeChecker_Env.open_universes_in env1.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____19516) with
| (tcenv', uu____19534, e_t) -> begin
(

let uu____19540 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____19551 -> begin
(failwith "Impossible")
end)
in (match (uu____19540) with
| (e1, t_norm1) -> begin
(((

let uu___149_19567 = env1
in {bindings = uu___149_19567.bindings; depth = uu___149_19567.depth; tcenv = tcenv'; warn = uu___149_19567.warn; cache = uu___149_19567.cache; nolabels = uu___149_19567.nolabels; use_zfuel_name = uu___149_19567.use_zfuel_name; encode_non_total_function_typ = uu___149_19567.encode_non_total_function_typ; current_module_name = uu___149_19567.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____19509) with
| (env', e1, t_norm1) -> begin
(

let uu____19577 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____19577) with
| ((binders, body, uu____19598, uu____19599), curry) -> begin
((

let uu____19610 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____19610) with
| true -> begin
(

let uu____19611 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____19612 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____19611 uu____19612)))
end
| uu____19613 -> begin
()
end));
(

let uu____19614 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____19614) with
| (vars, guards, env'1, binder_decls, uu____19641) -> begin
(

let body1 = (

let uu____19655 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____19655) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____19656 -> begin
body
end))
in (

let app = (mk_app1 curry f ftok vars)
in (

let uu____19658 = (

let uu____19667 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____19667) with
| true -> begin
(

let uu____19678 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____19679 = (encode_formula body1 env'1)
in ((uu____19678), (uu____19679))))
end
| uu____19688 -> begin
(

let uu____19689 = (encode_term body1 env'1)
in ((app), (uu____19689)))
end))
in (match (uu____19658) with
| (app1, (body2, decls2)) -> begin
(

let eqn = (

let uu____19712 = (

let uu____19719 = (

let uu____19720 = (

let uu____19731 = (FStar_SMTEncoding_Util.mkEq ((app1), (body2)))
in ((((app1)::[])::[]), (vars), (uu____19731)))
in (FStar_SMTEncoding_Util.mkForall uu____19720))
in (

let uu____19742 = (

let uu____19745 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____19745))
in ((uu____19719), (uu____19742), ((Prims.strcat "equation_" f)))))
in (FStar_SMTEncoding_Util.mkAssume uu____19712))
in (

let uu____19748 = (

let uu____19751 = (

let uu____19754 = (

let uu____19757 = (

let uu____19760 = (primitive_type_axioms env1.tcenv flid f app1)
in (FStar_List.append ((eqn)::[]) uu____19760))
in (FStar_List.append decls2 uu____19757))
in (FStar_List.append binder_decls uu____19754))
in (FStar_List.append decls1 uu____19751))
in ((uu____19748), (env1))))
end))))
end));
)
end))
end)))
end
| uu____19765 -> begin
(failwith "Impossible")
end)
end
| uu____19794 -> begin
(

let fuel = (

let uu____19800 = (varops.fresh "fuel")
in ((uu____19800), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env1
in (

let uu____19803 = (FStar_All.pipe_right toks1 (FStar_List.fold_left (fun uu____19891 uu____19892 -> (match (((uu____19891), (uu____19892))) with
| ((gtoks, env2), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (

let uu____20040 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____20040))
in (

let gtok = (

let uu____20042 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____20042))
in (

let env3 = (

let uu____20044 = (

let uu____20047 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42)) uu____20047))
in (push_free_var env2 flid gtok uu____20044))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env3))))))
end)) (([]), (env1))))
in (match (uu____19803) with
| (gtoks, env2) -> begin
(

let gtoks1 = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env01 uu____20203 t_norm uu____20205 -> (match (((uu____20203), (uu____20205))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____20249; FStar_Syntax_Syntax.lbeff = uu____20250; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let uu____20278 = (

let uu____20285 = (FStar_TypeChecker_Env.open_universes_in env2.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____20285) with
| (tcenv', uu____20307, e_t) -> begin
(

let uu____20313 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____20324 -> begin
(failwith "Impossible")
end)
in (match (uu____20313) with
| (e1, t_norm1) -> begin
(((

let uu___150_20340 = env2
in {bindings = uu___150_20340.bindings; depth = uu___150_20340.depth; tcenv = tcenv'; warn = uu___150_20340.warn; cache = uu___150_20340.cache; nolabels = uu___150_20340.nolabels; use_zfuel_name = uu___150_20340.use_zfuel_name; encode_non_total_function_typ = uu___150_20340.encode_non_total_function_typ; current_module_name = uu___150_20340.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____20278) with
| (env', e1, t_norm1) -> begin
((

let uu____20355 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____20355) with
| true -> begin
(

let uu____20356 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____20357 = (FStar_Syntax_Print.term_to_string t_norm1)
in (

let uu____20358 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____20356 uu____20357 uu____20358))))
end
| uu____20359 -> begin
()
end));
(

let uu____20360 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____20360) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____20397 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____20397) with
| true -> begin
(

let uu____20398 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____20399 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____20400 = (FStar_Syntax_Print.binders_to_string ", " formals)
in (

let uu____20401 = (FStar_Syntax_Print.term_to_string tres)
in (FStar_Util.print4 "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n" uu____20398 uu____20399 uu____20400 uu____20401)))))
end
| uu____20402 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____20404 -> begin
()
end);
(

let uu____20405 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____20405) with
| (vars, guards, env'1, binder_decls, uu____20436) -> begin
(

let decl_g = (

let uu____20450 = (

let uu____20461 = (

let uu____20464 = (FStar_List.map FStar_Pervasives_Native.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____20464)
in ((g), (uu____20461), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____20450))
in (

let env02 = (push_zfuel_name env01 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____20489 = (

let uu____20496 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____20496)))
in (FStar_SMTEncoding_Util.mkApp uu____20489))
in (

let gsapp = (

let uu____20506 = (

let uu____20513 = (

let uu____20516 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____20516)::vars_tm)
in ((g), (uu____20513)))
in (FStar_SMTEncoding_Util.mkApp uu____20506))
in (

let gmax = (

let uu____20522 = (

let uu____20529 = (

let uu____20532 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____20532)::vars_tm)
in ((g), (uu____20529)))
in (FStar_SMTEncoding_Util.mkApp uu____20522))
in (

let body1 = (

let uu____20538 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____20538) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____20539 -> begin
body
end))
in (

let uu____20540 = (encode_term body1 env'1)
in (match (uu____20540) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____20558 = (

let uu____20565 = (

let uu____20566 = (

let uu____20581 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____20581)))
in (FStar_SMTEncoding_Util.mkForall' uu____20566))
in (

let uu____20602 = (

let uu____20605 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____20605))
in ((uu____20565), (uu____20602), ((Prims.strcat "equation_with_fuel_" g)))))
in (FStar_SMTEncoding_Util.mkAssume uu____20558))
in (

let eqn_f = (

let uu____20609 = (

let uu____20616 = (

let uu____20617 = (

let uu____20628 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____20628)))
in (FStar_SMTEncoding_Util.mkForall uu____20617))
in ((uu____20616), (FStar_Pervasives_Native.Some ("Correspondence of recursive function to instrumented version")), ((Prims.strcat "@fuel_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____20609))
in (

let eqn_g' = (

let uu____20642 = (

let uu____20649 = (

let uu____20650 = (

let uu____20661 = (

let uu____20662 = (

let uu____20667 = (

let uu____20668 = (

let uu____20675 = (

let uu____20678 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____20678)::vars_tm)
in ((g), (uu____20675)))
in (FStar_SMTEncoding_Util.mkApp uu____20668))
in ((gsapp), (uu____20667)))
in (FStar_SMTEncoding_Util.mkEq uu____20662))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____20661)))
in (FStar_SMTEncoding_Util.mkForall uu____20650))
in ((uu____20649), (FStar_Pervasives_Native.Some ("Fuel irrelevance")), ((Prims.strcat "@fuel_irrelevance_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____20642))
in (

let uu____20701 = (

let uu____20710 = (encode_binders FStar_Pervasives_Native.None formals env02)
in (match (uu____20710) with
| (vars1, v_guards, env3, binder_decls1, uu____20739) -> begin
(

let vars_tm1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars1)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm1)))
in (

let tok_corr = (

let tok_app = (

let uu____20764 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____20764 ((fuel)::vars1)))
in (

let uu____20769 = (

let uu____20776 = (

let uu____20777 = (

let uu____20788 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars1), (uu____20788)))
in (FStar_SMTEncoding_Util.mkForall uu____20777))
in ((uu____20776), (FStar_Pervasives_Native.Some ("Fuel token correspondence")), ((Prims.strcat "fuel_token_correspondence_" gtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____20769)))
in (

let uu____20809 = (

let uu____20816 = (encode_term_pred FStar_Pervasives_Native.None tres env3 gapp)
in (match (uu____20816) with
| (g_typing, d3) -> begin
(

let uu____20829 = (

let uu____20832 = (

let uu____20833 = (

let uu____20840 = (

let uu____20841 = (

let uu____20852 = (

let uu____20853 = (

let uu____20858 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____20858), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____20853))
in ((((gapp)::[])::[]), ((fuel)::vars1), (uu____20852)))
in (FStar_SMTEncoding_Util.mkForall uu____20841))
in ((uu____20840), (FStar_Pervasives_Native.Some ("Typing correspondence of token to term")), ((Prims.strcat "token_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____20833))
in (uu____20832)::[])
in ((d3), (uu____20829)))
end))
in (match (uu____20809) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls1 aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____20701) with
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

let uu____20923 = (

let uu____20936 = (FStar_List.zip3 gtoks1 typs1 bindings)
in (FStar_List.fold_left (fun uu____21015 uu____21016 -> (match (((uu____21015), (uu____21016))) with
| ((decls2, eqns, env01), (gtok, ty, lb)) -> begin
(

let uu____21171 = (encode_one_binding env01 gtok ty lb)
in (match (uu____21171) with
| (decls', eqns', env02) -> begin
(((decls')::decls2), ((FStar_List.append eqns' eqns)), (env02))
end))
end)) (((decls1)::[]), ([]), (env0)) uu____20936))
in (match (uu____20923) with
| (decls2, eqns, env01) -> begin
(

let uu____21244 = (

let isDeclFun = (fun uu___117_21256 -> (match (uu___117_21256) with
| FStar_SMTEncoding_Term.DeclFun (uu____21257) -> begin
true
end
| uu____21268 -> begin
false
end))
in (

let uu____21269 = (FStar_All.pipe_right decls2 FStar_List.flatten)
in (FStar_All.pipe_right uu____21269 (FStar_List.partition isDeclFun))))
in (match (uu____21244) with
| (prefix_decls, rest) -> begin
(

let eqns1 = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns1))), (env01)))
end))
end))))
end)))))
end)
end))))))
end))
end))
end)
with
| Let_rec_unencodeable -> begin
(

let msg = (

let uu____21320 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____21320 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let nm = (

let uu____21369 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____21369) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____21373 = (encode_sigelt' env se)
in (match (uu____21373) with
| (g, env1) -> begin
(

let g1 = (match (g) with
| [] -> begin
(

let uu____21389 = (

let uu____21390 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____21390))
in (uu____21389)::[])
end
| uu____21391 -> begin
(

let uu____21392 = (

let uu____21395 = (

let uu____21396 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____21396))
in (uu____21395)::g)
in (

let uu____21397 = (

let uu____21400 = (

let uu____21401 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____21401))
in (uu____21400)::[])
in (FStar_List.append uu____21392 uu____21397)))
end)
in ((g1), (env1)))
end))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let is_opaque_to_smt = (fun t -> (

let uu____21414 = (

let uu____21415 = (FStar_Syntax_Subst.compress t)
in uu____21415.FStar_Syntax_Syntax.n)
in (match (uu____21414) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (bytes, uu____21419)) -> begin
((FStar_Util.string_of_bytes bytes) = "opaque_to_smt")
end
| uu____21424 -> begin
false
end)))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____21429) -> begin
(failwith "impossible -- removed by tc.fs")
end
| FStar_Syntax_Syntax.Sig_pragma (uu____21434) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_main (uu____21437) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____21440) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____21455) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____21459 = (

let uu____21460 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____21460 Prims.op_Negation))
in (match (uu____21459) with
| true -> begin
(([]), (env))
end
| uu____21469 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____21486 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((ed.FStar_Syntax_Syntax.binders), (tm), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end))
in (

let encode_action = (fun env1 a -> (

let uu____21506 = (new_term_constant_and_tok_from_lid env1 a.FStar_Syntax_Syntax.action_name)
in (match (uu____21506) with
| (aname, atok, env2) -> begin
(

let uu____21522 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____21522) with
| (formals, uu____21540) -> begin
(

let uu____21553 = (

let uu____21558 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____21558 env2))
in (match (uu____21553) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____21570 = (

let uu____21571 = (

let uu____21582 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____21598 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____21582), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____21571))
in (uu____21570)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action token")))))::[])
in (

let uu____21611 = (

let aux = (fun uu____21663 uu____21664 -> (match (((uu____21663), (uu____21664))) with
| ((bv, uu____21716), (env3, acc_sorts, acc)) -> begin
(

let uu____21754 = (gen_term_var env3 bv)
in (match (uu____21754) with
| (xxsym, xx, env4) -> begin
((env4), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::acc_sorts), ((xx)::acc))
end))
end))
in (FStar_List.fold_right aux formals ((env2), ([]), ([]))))
in (match (uu____21611) with
| (uu____21826, xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (

let a_eq = (

let uu____21849 = (

let uu____21856 = (

let uu____21857 = (

let uu____21868 = (

let uu____21869 = (

let uu____21874 = (mk_Apply tm xs_sorts)
in ((app), (uu____21874)))
in (FStar_SMTEncoding_Util.mkEq uu____21869))
in ((((app)::[])::[]), (xs_sorts), (uu____21868)))
in (FStar_SMTEncoding_Util.mkForall uu____21857))
in ((uu____21856), (FStar_Pervasives_Native.Some ("Action equality")), ((Prims.strcat aname "_equality"))))
in (FStar_SMTEncoding_Util.mkAssume uu____21849))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____21894 = (

let uu____21901 = (

let uu____21902 = (

let uu____21913 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____21913)))
in (FStar_SMTEncoding_Util.mkForall uu____21902))
in ((uu____21901), (FStar_Pervasives_Native.Some ("Action token correspondence")), ((Prims.strcat aname "_token_correspondence"))))
in (FStar_SMTEncoding_Util.mkAssume uu____21894))))
in ((env2), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____21932 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____21932) with
| (env1, decls2) -> begin
(((FStar_List.flatten decls2)), (env1))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____21960, uu____21961) when (FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid) -> begin
(

let uu____21962 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____21962) with
| (tname, ttok, env1) -> begin
(([]), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____21979, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let will_encode_definition = (

let uu____21985 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___118_21989 -> (match (uu___118_21989) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____21990) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____21995) -> begin
true
end
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____21996 -> begin
false
end))))
in (not (uu____21985)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____22003 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____22005 = (encode_top_level_val env fv t quals)
in (match (uu____22005) with
| (decls, env1) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____22024 = (

let uu____22027 = (primitive_type_axioms env1.tcenv lid tname tsym)
in (FStar_List.append decls uu____22027))
in ((uu____22024), (env1)))))
end)))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, f) -> begin
(

let uu____22035 = (FStar_Syntax_Subst.open_univ_vars us f)
in (match (uu____22035) with
| (uu____22044, f1) -> begin
(

let uu____22046 = (encode_formula f1 env)
in (match (uu____22046) with
| (f2, decls) -> begin
(

let g = (

let uu____22060 = (

let uu____22061 = (

let uu____22068 = (

let uu____22071 = (

let uu____22072 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____22072))
in FStar_Pervasives_Native.Some (uu____22071))
in (

let uu____22073 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in ((f2), (uu____22068), (uu____22073))))
in (FStar_SMTEncoding_Util.mkAssume uu____22061))
in (uu____22060)::[])
in (((FStar_List.append decls g)), (env)))
end))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____22079) when ((FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) || (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_opaque_to_smt))) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let uu____22091 = (FStar_Util.fold_map (fun env1 lb -> (

let lid = (

let uu____22109 = (

let uu____22112 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____22112.FStar_Syntax_Syntax.fv_name)
in uu____22109.FStar_Syntax_Syntax.v)
in (

let uu____22113 = (

let uu____22114 = (FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____22114))
in (match (uu____22113) with
| true -> begin
(

let val_decl = (

let uu___151_22142 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___151_22142.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Irreducible)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___151_22142.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___151_22142.FStar_Syntax_Syntax.sigattrs})
in (

let uu____22147 = (encode_sigelt' env1 val_decl)
in (match (uu____22147) with
| (decls, env2) -> begin
((env2), (decls))
end)))
end
| uu____22158 -> begin
((env1), ([]))
end)))) env (FStar_Pervasives_Native.snd lbs))
in (match (uu____22091) with
| (env1, decls) -> begin
(((FStar_List.flatten decls)), (env1))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((uu____22175, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t1); FStar_Syntax_Syntax.lbunivs = uu____22177; FStar_Syntax_Syntax.lbtyp = uu____22178; FStar_Syntax_Syntax.lbeff = uu____22179; FStar_Syntax_Syntax.lbdef = uu____22180})::[]), uu____22181) when (FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid) -> begin
(

let uu____22200 = (new_term_constant_and_tok_from_lid env b2t1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____22200) with
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

let uu____22229 = (

let uu____22232 = (

let uu____22233 = (

let uu____22240 = (

let uu____22241 = (

let uu____22252 = (

let uu____22253 = (

let uu____22258 = (FStar_SMTEncoding_Util.mkApp (((FStar_Pervasives_Native.snd FStar_SMTEncoding_Term.boxBoolFun)), ((x)::[])))
in ((valid_b2t_x), (uu____22258)))
in (FStar_SMTEncoding_Util.mkEq uu____22253))
in ((((b2t_x)::[])::[]), ((xx)::[]), (uu____22252)))
in (FStar_SMTEncoding_Util.mkForall uu____22241))
in ((uu____22240), (FStar_Pervasives_Native.Some ("b2t def")), ("b2t_def")))
in (FStar_SMTEncoding_Util.mkAssume uu____22233))
in (uu____22232)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None))))::uu____22229)
in ((decls), (env1)))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____22291, uu____22292) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___119_22301 -> (match (uu___119_22301) with
| FStar_Syntax_Syntax.Discriminator (uu____22302) -> begin
true
end
| uu____22303 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____22306, lids) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____22317 = (

let uu____22318 = (FStar_List.hd l.FStar_Ident.ns)
in uu____22318.FStar_Ident.idText)
in (uu____22317 = "Prims"))))) && (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___120_22322 -> (match (uu___120_22322) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____22323 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____22327) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___121_22344 -> (match (uu___121_22344) with
| FStar_Syntax_Syntax.Projector (uu____22345) -> begin
true
end
| uu____22350 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____22353 = (try_lookup_free_var env l)
in (match (uu____22353) with
| FStar_Pervasives_Native.Some (uu____22360) -> begin
(([]), (env))
end
| FStar_Pervasives_Native.None -> begin
(

let se1 = (

let uu___152_22364 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l); FStar_Syntax_Syntax.sigquals = uu___152_22364.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___152_22364.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___152_22364.FStar_Syntax_Syntax.sigattrs})
in (encode_sigelt env se1))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____22371) -> begin
(encode_top_level_let env ((is_rec), (bindings)) se.FStar_Syntax_Syntax.sigquals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____22389) -> begin
(

let uu____22398 = (encode_sigelts env ses)
in (match (uu____22398) with
| (g, env1) -> begin
(

let uu____22415 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___122_22438 -> (match (uu___122_22438) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = uu____22439; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("inversion axiom"); FStar_SMTEncoding_Term.assumption_name = uu____22440; FStar_SMTEncoding_Term.assumption_fact_ids = uu____22441}) -> begin
false
end
| uu____22444 -> begin
true
end))))
in (match (uu____22415) with
| (g', inversions) -> begin
(

let uu____22459 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___123_22480 -> (match (uu___123_22480) with
| FStar_SMTEncoding_Term.DeclFun (uu____22481) -> begin
true
end
| uu____22492 -> begin
false
end))))
in (match (uu____22459) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env1))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____22510, tps, k, uu____22513, datas) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___124_22530 -> (match (uu___124_22530) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____22531 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____22540 = c
in (match (uu____22540) with
| (name, args, uu____22545, uu____22546, uu____22547) -> begin
(

let uu____22552 = (

let uu____22553 = (

let uu____22564 = (FStar_All.pipe_right args (FStar_List.map (fun uu____22581 -> (match (uu____22581) with
| (uu____22588, sort, uu____22590) -> begin
sort
end))))
in ((name), (uu____22564), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____22553))
in (uu____22552)::[])
end))
end
| uu____22595 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____22617 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____22623 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____22623 FStar_Option.isNone)))))
in (match (uu____22617) with
| true -> begin
[]
end
| uu____22654 -> begin
(

let uu____22655 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____22655) with
| (xxsym, xx) -> begin
(

let uu____22664 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____22703 l -> (match (uu____22703) with
| (out, decls) -> begin
(

let uu____22723 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____22723) with
| (uu____22734, data_t) -> begin
(

let uu____22736 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____22736) with
| (args, res) -> begin
(

let indices = (

let uu____22782 = (

let uu____22783 = (FStar_Syntax_Subst.compress res)
in uu____22783.FStar_Syntax_Syntax.n)
in (match (uu____22782) with
| FStar_Syntax_Syntax.Tm_app (uu____22794, indices) -> begin
indices
end
| uu____22816 -> begin
[]
end))
in (

let env1 = (FStar_All.pipe_right args (FStar_List.fold_left (fun env1 uu____22840 -> (match (uu____22840) with
| (x, uu____22846) -> begin
(

let uu____22847 = (

let uu____22848 = (

let uu____22855 = (mk_term_projector_name l x)
in ((uu____22855), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____22848))
in (push_term_var env1 x uu____22847))
end)) env))
in (

let uu____22858 = (encode_args indices env1)
in (match (uu____22858) with
| (indices1, decls') -> begin
((match (((FStar_List.length indices1) <> (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____22882 -> begin
()
end);
(

let eqs = (

let uu____22884 = (FStar_List.map2 (fun v1 a -> (

let uu____22900 = (

let uu____22905 = (FStar_SMTEncoding_Util.mkFreeV v1)
in ((uu____22905), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____22900))) vars indices1)
in (FStar_All.pipe_right uu____22884 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____22908 = (

let uu____22909 = (

let uu____22914 = (

let uu____22915 = (

let uu____22920 = (mk_data_tester env1 l xx)
in ((uu____22920), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____22915))
in ((out), (uu____22914)))
in (FStar_SMTEncoding_Util.mkOr uu____22909))
in ((uu____22908), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____22664) with
| (data_ax, decls) -> begin
(

let uu____22933 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____22933) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____22944 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____22944 xx tapp))
end
| uu____22947 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____22948 = (

let uu____22955 = (

let uu____22956 = (

let uu____22967 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____22982 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____22967), (uu____22982))))
in (FStar_SMTEncoding_Util.mkForall uu____22956))
in (

let uu____22997 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in ((uu____22955), (FStar_Pervasives_Native.Some ("inversion axiom")), (uu____22997))))
in (FStar_SMTEncoding_Util.mkAssume uu____22948)))
in (

let pattern_guarded_inversion = (

let uu____23003 = ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1")))
in (match (uu____23003) with
| true -> begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (

let uu____23010 = (

let uu____23011 = (

let uu____23018 = (

let uu____23019 = (

let uu____23030 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____23045 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (uu____23030), (uu____23045))))
in (FStar_SMTEncoding_Util.mkForall uu____23019))
in (

let uu____23060 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in ((uu____23018), (FStar_Pervasives_Native.Some ("inversion axiom")), (uu____23060))))
in (FStar_SMTEncoding_Util.mkAssume uu____23011))
in (uu____23010)::[])))
end
| uu____23063 -> begin
[]
end))
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)))
in (

let uu____23064 = (

let uu____23077 = (

let uu____23078 = (FStar_Syntax_Subst.compress k)
in uu____23078.FStar_Syntax_Syntax.n)
in (match (uu____23077) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____23123 -> begin
((tps), (k))
end))
in (match (uu____23064) with
| (formals, res) -> begin
(

let uu____23146 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____23146) with
| (formals1, res1) -> begin
(

let uu____23157 = (encode_binders FStar_Pervasives_Native.None formals1 env)
in (match (uu____23157) with
| (vars, guards, env', binder_decls, uu____23182) -> begin
(

let uu____23195 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____23195) with
| (tname, ttok, env1) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____23214 = (

let uu____23221 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____23221)))
in (FStar_SMTEncoding_Util.mkApp uu____23214))
in (

let uu____23230 = (

let tname_decl = (

let uu____23240 = (

let uu____23241 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____23273 -> (match (uu____23273) with
| (n1, s) -> begin
(((Prims.strcat tname n1)), (s), (false))
end))))
in (

let uu____23286 = (varops.next_id ())
in ((tname), (uu____23241), (FStar_SMTEncoding_Term.Term_sort), (uu____23286), (false))))
in (constructor_or_logic_type_decl uu____23240))
in (

let uu____23295 = (match (vars) with
| [] -> begin
(

let uu____23308 = (

let uu____23309 = (

let uu____23312 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_43 -> FStar_Pervasives_Native.Some (_0_43)) uu____23312))
in (push_free_var env1 t tname uu____23309))
in (([]), (uu____23308)))
end
| uu____23319 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("token"))))
in (

let ttok_fresh = (

let uu____23328 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____23328))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____23342 = (

let uu____23349 = (

let uu____23350 = (

let uu____23365 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (FStar_Pervasives_Native.None), (vars), (uu____23365)))
in (FStar_SMTEncoding_Util.mkForall' uu____23350))
in ((uu____23349), (FStar_Pervasives_Native.Some ("name-token correspondence")), ((Prims.strcat "token_correspondence_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____23342))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env1)))))))
end)
in (match (uu____23295) with
| (tok_decls, env2) -> begin
(((FStar_List.append tname_decl tok_decls)), (env2))
end)))
in (match (uu____23230) with
| (decls, env2) -> begin
(

let kindingAx = (

let uu____23405 = (encode_term_pred FStar_Pervasives_Native.None res1 env' tapp)
in (match (uu____23405) with
| (k1, decls1) -> begin
(

let karr = (match (((FStar_List.length formals1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____23423 = (

let uu____23424 = (

let uu____23431 = (

let uu____23432 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____23432))
in ((uu____23431), (FStar_Pervasives_Native.Some ("kinding")), ((Prims.strcat "pre_kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____23424))
in (uu____23423)::[])
end
| uu____23435 -> begin
[]
end)
in (

let uu____23436 = (

let uu____23439 = (

let uu____23442 = (

let uu____23443 = (

let uu____23450 = (

let uu____23451 = (

let uu____23462 = (FStar_SMTEncoding_Util.mkImp ((guard), (k1)))
in ((((tapp)::[])::[]), (vars), (uu____23462)))
in (FStar_SMTEncoding_Util.mkForall uu____23451))
in ((uu____23450), (FStar_Pervasives_Native.None), ((Prims.strcat "kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____23443))
in (uu____23442)::[])
in (FStar_List.append karr uu____23439))
in (FStar_List.append decls1 uu____23436)))
end))
in (

let aux = (

let uu____23478 = (

let uu____23481 = (inversion_axioms tapp vars)
in (

let uu____23484 = (

let uu____23487 = (pretype_axiom env2 tapp vars)
in (uu____23487)::[])
in (FStar_List.append uu____23481 uu____23484)))
in (FStar_List.append kindingAx uu____23478))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env2)))))
end)))))
end))
end))
end))
end))))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____23494, uu____23495, uu____23496, uu____23497, uu____23498) when (FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____23506, t, uu____23508, n_tps, uu____23510) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____23518 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____23518) with
| (ddconstrsym, ddtok, env1) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____23535 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____23535) with
| (formals, t_res) -> begin
(

let uu____23570 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____23570) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____23584 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____23584) with
| (vars, guards, env', binder_decls, names1) -> begin
(

let fields = (FStar_All.pipe_right names1 (FStar_List.mapi (fun n1 x -> (

let projectible = true
in (

let uu____23654 = (mk_term_projector_name d x)
in ((uu____23654), (FStar_SMTEncoding_Term.Term_sort), (projectible)))))))
in (

let datacons = (

let uu____23656 = (

let uu____23675 = (varops.next_id ())
in ((ddconstrsym), (fields), (FStar_SMTEncoding_Term.Term_sort), (uu____23675), (true)))
in (FStar_All.pipe_right uu____23656 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____23714 = (encode_term_pred FStar_Pervasives_Native.None t env1 ddtok_tm)
in (match (uu____23714) with
| (tok_typing, decls3) -> begin
(

let tok_typing1 = (match (fields) with
| (uu____23726)::uu____23727 -> begin
(

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (mk_Apply ddtok_tm ((ff)::[]))
in (

let vtok_app_r = (mk_Apply f ((((ddtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let uu____23772 = (

let uu____23783 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____23783)))
in (FStar_SMTEncoding_Util.mkForall uu____23772))))))
end
| uu____23808 -> begin
tok_typing
end)
in (

let uu____23817 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____23817) with
| (vars', guards', env'', decls_formals, uu____23842) -> begin
(

let uu____23855 = (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (encode_term_pred (FStar_Pervasives_Native.Some (fuel_tm)) t_res env'' dapp1)))
in (match (uu____23855) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____23886 -> begin
(

let uu____23893 = (

let uu____23894 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____23894))
in (uu____23893)::[])
end)
in (

let encode_elim = (fun uu____23904 -> (

let uu____23905 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____23905) with
| (head1, args) -> begin
(

let uu____23948 = (

let uu____23949 = (FStar_Syntax_Subst.compress head1)
in uu____23949.FStar_Syntax_Syntax.n)
in (match (uu____23948) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____23959; FStar_Syntax_Syntax.vars = uu____23960}, uu____23961) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____23967 = (encode_args args env')
in (match (uu____23967) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____24010 -> begin
(

let uu____24011 = (

let uu____24012 = (

let uu____24017 = (

let uu____24018 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____24018))
in ((uu____24017), (orig_arg.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____24012))
in (FStar_Pervasives.raise uu____24011))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____24034 = (

let uu____24035 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____24035))
in (match (uu____24034) with
| true -> begin
(

let uu____24048 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____24048)::[])
end
| uu____24049 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____24050 = (

let uu____24063 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____24113 uu____24114 -> (match (((uu____24113), (uu____24114))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____24209 = (

let uu____24216 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____24216))
in (match (uu____24209) with
| (uu____24229, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____24237 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____24237)::eqns_or_guards)
end
| uu____24238 -> begin
(

let uu____24239 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____24239)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____24063))
in (match (uu____24050) with
| (uu____24254, arg_vars, elim_eqns_or_guards, uu____24257) -> begin
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

let uu____24287 = (

let uu____24294 = (

let uu____24295 = (

let uu____24306 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____24317 = (

let uu____24318 = (

let uu____24323 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____24323)))
in (FStar_SMTEncoding_Util.mkImp uu____24318))
in ((((ty_pred)::[])::[]), (uu____24306), (uu____24317))))
in (FStar_SMTEncoding_Util.mkForall uu____24295))
in ((uu____24294), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____24287))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____24346 = (varops.fresh "x")
in ((uu____24346), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____24348 = (

let uu____24355 = (

let uu____24356 = (

let uu____24367 = (

let uu____24372 = (

let uu____24375 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____24375)::[])
in (uu____24372)::[])
in (

let uu____24380 = (

let uu____24381 = (

let uu____24386 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____24387 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____24386), (uu____24387))))
in (FStar_SMTEncoding_Util.mkImp uu____24381))
in ((uu____24367), ((x)::[]), (uu____24380))))
in (FStar_SMTEncoding_Util.mkForall uu____24356))
in (

let uu____24406 = (varops.mk_unique "lextop")
in ((uu____24355), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____24406))))
in (FStar_SMTEncoding_Util.mkAssume uu____24348))))
end
| uu____24409 -> begin
(

let prec = (

let uu____24413 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____24440 -> begin
(

let uu____24441 = (

let uu____24442 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____24442 dapp1))
in (uu____24441)::[])
end))))
in (FStar_All.pipe_right uu____24413 FStar_List.flatten))
in (

let uu____24449 = (

let uu____24456 = (

let uu____24457 = (

let uu____24468 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____24479 = (

let uu____24480 = (

let uu____24485 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____24485)))
in (FStar_SMTEncoding_Util.mkImp uu____24480))
in ((((ty_pred)::[])::[]), (uu____24468), (uu____24479))))
in (FStar_SMTEncoding_Util.mkForall uu____24457))
in ((uu____24456), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____24449)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____24506 = (encode_args args env')
in (match (uu____24506) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____24549 -> begin
(

let uu____24550 = (

let uu____24551 = (

let uu____24556 = (

let uu____24557 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____24557))
in ((uu____24556), (orig_arg.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____24551))
in (FStar_Pervasives.raise uu____24550))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____24573 = (

let uu____24574 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____24574))
in (match (uu____24573) with
| true -> begin
(

let uu____24587 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____24587)::[])
end
| uu____24588 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____24589 = (

let uu____24602 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____24652 uu____24653 -> (match (((uu____24652), (uu____24653))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____24748 = (

let uu____24755 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____24755))
in (match (uu____24748) with
| (uu____24768, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____24776 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____24776)::eqns_or_guards)
end
| uu____24777 -> begin
(

let uu____24778 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____24778)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____24602))
in (match (uu____24589) with
| (uu____24793, arg_vars, elim_eqns_or_guards, uu____24796) -> begin
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

let uu____24826 = (

let uu____24833 = (

let uu____24834 = (

let uu____24845 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____24856 = (

let uu____24857 = (

let uu____24862 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____24862)))
in (FStar_SMTEncoding_Util.mkImp uu____24857))
in ((((ty_pred)::[])::[]), (uu____24845), (uu____24856))))
in (FStar_SMTEncoding_Util.mkForall uu____24834))
in ((uu____24833), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____24826))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____24885 = (varops.fresh "x")
in ((uu____24885), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____24887 = (

let uu____24894 = (

let uu____24895 = (

let uu____24906 = (

let uu____24911 = (

let uu____24914 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____24914)::[])
in (uu____24911)::[])
in (

let uu____24919 = (

let uu____24920 = (

let uu____24925 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____24926 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____24925), (uu____24926))))
in (FStar_SMTEncoding_Util.mkImp uu____24920))
in ((uu____24906), ((x)::[]), (uu____24919))))
in (FStar_SMTEncoding_Util.mkForall uu____24895))
in (

let uu____24945 = (varops.mk_unique "lextop")
in ((uu____24894), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____24945))))
in (FStar_SMTEncoding_Util.mkAssume uu____24887))))
end
| uu____24948 -> begin
(

let prec = (

let uu____24952 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____24979 -> begin
(

let uu____24980 = (

let uu____24981 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____24981 dapp1))
in (uu____24980)::[])
end))))
in (FStar_All.pipe_right uu____24952 FStar_List.flatten))
in (

let uu____24988 = (

let uu____24995 = (

let uu____24996 = (

let uu____25007 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25018 = (

let uu____25019 = (

let uu____25024 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____25024)))
in (FStar_SMTEncoding_Util.mkImp uu____25019))
in ((((ty_pred)::[])::[]), (uu____25007), (uu____25018))))
in (FStar_SMTEncoding_Util.mkForall uu____24996))
in ((uu____24995), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____24988)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| uu____25043 -> begin
((

let uu____25045 = (

let uu____25046 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____25047 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____25046 uu____25047)))
in (FStar_Errors.warn se.FStar_Syntax_Syntax.sigrng uu____25045));
(([]), ([]));
)
end))
end)))
in (

let uu____25052 = (encode_elim ())
in (match (uu____25052) with
| (decls2, elim) -> begin
(

let g = (

let uu____25072 = (

let uu____25075 = (

let uu____25078 = (

let uu____25081 = (

let uu____25084 = (

let uu____25085 = (

let uu____25096 = (

let uu____25099 = (

let uu____25100 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____25100))
in FStar_Pervasives_Native.Some (uu____25099))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____25096)))
in FStar_SMTEncoding_Term.DeclFun (uu____25085))
in (uu____25084)::[])
in (

let uu____25105 = (

let uu____25108 = (

let uu____25111 = (

let uu____25114 = (

let uu____25117 = (

let uu____25120 = (

let uu____25123 = (

let uu____25124 = (

let uu____25131 = (

let uu____25132 = (

let uu____25143 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____25143)))
in (FStar_SMTEncoding_Util.mkForall uu____25132))
in ((uu____25131), (FStar_Pervasives_Native.Some ("equality for proxy")), ((Prims.strcat "equality_tok_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____25124))
in (

let uu____25156 = (

let uu____25159 = (

let uu____25160 = (

let uu____25167 = (

let uu____25168 = (

let uu____25179 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____25190 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____25179), (uu____25190))))
in (FStar_SMTEncoding_Util.mkForall uu____25168))
in ((uu____25167), (FStar_Pervasives_Native.Some ("data constructor typing intro")), ((Prims.strcat "data_typing_intro_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____25160))
in (uu____25159)::[])
in (uu____25123)::uu____25156))
in ((FStar_SMTEncoding_Util.mkAssume ((tok_typing1), (FStar_Pervasives_Native.Some ("typing for data constructor proxy")), ((Prims.strcat "typing_tok_" ddtok)))))::uu____25120)
in (FStar_List.append uu____25117 elim))
in (FStar_List.append decls_pred uu____25114))
in (FStar_List.append decls_formals uu____25111))
in (FStar_List.append proxy_fresh uu____25108))
in (FStar_List.append uu____25081 uu____25105)))
in (FStar_List.append decls3 uu____25078))
in (FStar_List.append decls2 uu____25075))
in (FStar_List.append binder_decls uu____25072))
in (((FStar_List.append datacons g)), (env1)))
end)))))
end))
end)))
end))))))))
end)))
end))
end)))
end)))
end)))
and encode_sigelts : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____25236 se -> (match (uu____25236) with
| (g, env1) -> begin
(

let uu____25256 = (encode_sigelt env1 se)
in (match (uu____25256) with
| (g', env2) -> begin
(((FStar_List.append g g')), (env2))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____25315 -> (match (uu____25315) with
| (i, decls, env1) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____25347) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env1))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____25353 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____25353) with
| true -> begin
(

let uu____25354 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____25355 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____25356 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____25354 uu____25355 uu____25356))))
end
| uu____25357 -> begin
()
end));
(

let uu____25358 = (encode_term t1 env1)
in (match (uu____25358) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____25374 = (

let uu____25381 = (

let uu____25382 = (

let uu____25383 = (FStar_Util.digest_of_string t_hash)
in (Prims.strcat uu____25383 (Prims.strcat "_" (Prims.string_of_int i))))
in (Prims.strcat "x_" uu____25382))
in (new_term_constant_from_string env1 x uu____25381))
in (match (uu____25374) with
| (xxsym, xx, env') -> begin
(

let t2 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel FStar_Pervasives_Native.None xx t)
in (

let caption = (

let uu____25399 = (FStar_Options.log_queries ())
in (match (uu____25399) with
| true -> begin
(

let uu____25402 = (

let uu____25403 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____25404 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____25405 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____25403 uu____25404 uu____25405))))
in FStar_Pervasives_Native.Some (uu____25402))
end
| uu____25406 -> begin
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
| FStar_TypeChecker_Env.Binding_lid (x, (uu____25421, t)) -> begin
(

let t_norm = (whnf env1 t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____25435 = (encode_free_var env1 fv t t_norm [])
in (match (uu____25435) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| FStar_TypeChecker_Env.Binding_sig_inst (uu____25458, se, uu____25460) -> begin
(

let uu____25465 = (encode_sigelt env1 se)
in (match (uu____25465) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end
| FStar_TypeChecker_Env.Binding_sig (uu____25482, se) -> begin
(

let uu____25488 = (encode_sigelt env1 se)
in (match (uu____25488) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____25505 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____25505) with
| (uu____25528, decls, env1) -> begin
((decls), (env1))
end))))


let encode_labels : 'Auu____25543 'Auu____25544 . ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____25544 * 'Auu____25543) Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl Prims.list) = (fun labs -> (

let prefix1 = (FStar_All.pipe_right labs (FStar_List.map (fun uu____25612 -> (match (uu____25612) with
| (l, uu____25624, uu____25625) -> begin
FStar_SMTEncoding_Term.DeclFun ((((FStar_Pervasives_Native.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (FStar_Pervasives_Native.None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____25671 -> (match (uu____25671) with
| (l, uu____25685, uu____25686) -> begin
(

let uu____25695 = (FStar_All.pipe_left (fun _0_44 -> FStar_SMTEncoding_Term.Echo (_0_44)) (FStar_Pervasives_Native.fst l))
in (

let uu____25696 = (

let uu____25699 = (

let uu____25700 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____25700))
in (uu____25699)::[])
in (uu____25695)::uu____25696))
end))))
in ((prefix1), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____25716 = (

let uu____25719 = (

let uu____25720 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____25723 = (

let uu____25724 = (FStar_TypeChecker_Env.current_module tcenv)
in (FStar_All.pipe_right uu____25724 FStar_Ident.string_of_lid))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____25720; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true; current_module_name = uu____25723}))
in (uu____25719)::[])
in (FStar_ST.write last_env uu____25716)))


let get_env : FStar_Ident.lident  ->  FStar_TypeChecker_Env.env  ->  env_t = (fun cmn tcenv -> (

let uu____25735 = (FStar_ST.read last_env)
in (match (uu____25735) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____25741 -> begin
(

let uu___153_25744 = e
in (

let uu____25745 = (FStar_Ident.string_of_lid cmn)
in {bindings = uu___153_25744.bindings; depth = uu___153_25744.depth; tcenv = tcenv; warn = uu___153_25744.warn; cache = uu___153_25744.cache; nolabels = uu___153_25744.nolabels; use_zfuel_name = uu___153_25744.use_zfuel_name; encode_non_total_function_typ = uu___153_25744.encode_non_total_function_typ; current_module_name = uu____25745}))
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____25750 = (FStar_ST.read last_env)
in (match (uu____25750) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____25755)::tl1 -> begin
(FStar_ST.write last_env ((env)::tl1))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____25764 -> (

let uu____25765 = (FStar_ST.read last_env)
in (match (uu____25765) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd1)::tl1 -> begin
(

let refs = (FStar_Util.smap_copy hd1.cache)
in (

let top = (

let uu___154_25778 = hd1
in {bindings = uu___154_25778.bindings; depth = uu___154_25778.depth; tcenv = uu___154_25778.tcenv; warn = uu___154_25778.warn; cache = refs; nolabels = uu___154_25778.nolabels; use_zfuel_name = uu___154_25778.use_zfuel_name; encode_non_total_function_typ = uu___154_25778.encode_non_total_function_typ; current_module_name = uu___154_25778.current_module_name})
in (FStar_ST.write last_env ((top)::(hd1)::tl1))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____25784 -> (

let uu____25785 = (FStar_ST.read last_env)
in (match (uu____25785) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____25790)::tl1 -> begin
(FStar_ST.write last_env tl1)
end)))


let mark_env : Prims.unit  ->  Prims.unit = (fun uu____25799 -> (push_env ()))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun uu____25803 -> (pop_env ()))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun uu____25807 -> (

let uu____25808 = (FStar_ST.read last_env)
in (match (uu____25808) with
| (hd1)::(uu____25814)::tl1 -> begin
(FStar_ST.write last_env ((hd1)::tl1))
end
| uu____25820 -> begin
(failwith "Impossible")
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


let mark : Prims.string  ->  Prims.unit = (fun msg -> ((mark_env ());
(varops.mark ());
(FStar_SMTEncoding_Z3.mark msg);
))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> ((reset_mark_env ());
(varops.reset_mark ());
(FStar_SMTEncoding_Z3.reset_mark msg);
))


let commit_mark : Prims.string  ->  Prims.unit = (fun msg -> ((commit_mark_env ());
(varops.commit_mark ());
(FStar_SMTEncoding_Z3.commit_mark msg);
))


let open_fact_db_tags : env_t  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env -> [])


let place_decl_in_fact_dbs : env_t  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl = (fun env fact_db_ids d -> (match (((fact_db_ids), (d))) with
| ((uu____25885)::uu____25886, FStar_SMTEncoding_Term.Assume (a)) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___155_25894 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___155_25894.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = uu___155_25894.FStar_SMTEncoding_Term.assumption_caption; FStar_SMTEncoding_Term.assumption_name = uu___155_25894.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids}))
end
| uu____25895 -> begin
d
end))


let fact_dbs_for_lid : env_t  ->  FStar_Ident.lid  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env lid -> (

let uu____25912 = (

let uu____25915 = (

let uu____25916 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_SMTEncoding_Term.Namespace (uu____25916))
in (

let uu____25917 = (open_fact_db_tags env)
in (uu____25915)::uu____25917))
in (FStar_SMTEncoding_Term.Name (lid))::uu____25912))


let encode_top_level_facts : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env se -> (

let fact_db_ids = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.collect (fact_dbs_for_lid env)))
in (

let uu____25941 = (encode_sigelt env se)
in (match (uu____25941) with
| (g, env1) -> begin
(

let g1 = (FStar_All.pipe_right g (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)))
in ((g1), (env1)))
end))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> (

let uu____25979 = (FStar_Options.log_queries ())
in (match (uu____25979) with
| true -> begin
(

let uu____25982 = (

let uu____25983 = (

let uu____25984 = (

let uu____25985 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____25985 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____25984))
in FStar_SMTEncoding_Term.Caption (uu____25983))
in (uu____25982)::decls)
end
| uu____25994 -> begin
decls
end)))
in (

let env = (

let uu____25996 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____25996 tcenv))
in (

let uu____25997 = (encode_top_level_facts env se)
in (match (uu____25997) with
| (decls, env1) -> begin
((set_env env1);
(

let uu____26011 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____26011));
)
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____26023 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____26025 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____26025) with
| true -> begin
(

let uu____26026 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) Prims.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____26026))
end
| uu____26027 -> begin
()
end));
(

let env = (get_env modul.FStar_Syntax_Syntax.name tcenv)
in (

let encode_signature = (fun env1 ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____26061 se -> (match (uu____26061) with
| (g, env2) -> begin
(

let uu____26081 = (encode_top_level_facts env2 se)
in (match (uu____26081) with
| (g', env3) -> begin
(((FStar_List.append g g')), (env3))
end))
end)) (([]), (env1)))))
in (

let uu____26104 = (encode_signature (

let uu___156_26113 = env
in {bindings = uu___156_26113.bindings; depth = uu___156_26113.depth; tcenv = uu___156_26113.tcenv; warn = false; cache = uu___156_26113.cache; nolabels = uu___156_26113.nolabels; use_zfuel_name = uu___156_26113.use_zfuel_name; encode_non_total_function_typ = uu___156_26113.encode_non_total_function_typ; current_module_name = uu___156_26113.current_module_name}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____26104) with
| (decls, env1) -> begin
(

let caption = (fun decls1 -> (

let uu____26130 = (FStar_Options.log_queries ())
in (match (uu____26130) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls1) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____26134 -> begin
decls1
end)))
in ((set_env (

let uu___157_26138 = env1
in {bindings = uu___157_26138.bindings; depth = uu___157_26138.depth; tcenv = uu___157_26138.tcenv; warn = true; cache = uu___157_26138.cache; nolabels = uu___157_26138.nolabels; use_zfuel_name = uu___157_26138.use_zfuel_name; encode_non_total_function_typ = uu___157_26138.encode_non_total_function_typ; current_module_name = uu___157_26138.current_module_name}));
(

let uu____26140 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____26140) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____26141 -> begin
()
end));
(

let decls1 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls1));
))
end))));
)))


let encode_query : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____26195 = (

let uu____26196 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____26196.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____26195));
(

let env = (

let uu____26198 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____26198 tcenv))
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____26210 = (

let rec aux = (fun bindings1 -> (match (bindings1) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____26245 = (aux rest)
in (match (uu____26245) with
| (out, rest1) -> begin
(

let t = (

let uu____26275 = (FStar_Syntax_Util.destruct_typ_as_formula x.FStar_Syntax_Syntax.sort)
in (match (uu____26275) with
| FStar_Pervasives_Native.Some (uu____26280) -> begin
(

let uu____26281 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Util.refine uu____26281 x.FStar_Syntax_Syntax.sort))
end
| uu____26282 -> begin
x.FStar_Syntax_Syntax.sort
end))
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
in (

let uu____26286 = (

let uu____26289 = (FStar_Syntax_Syntax.mk_binder (

let uu___158_26292 = x
in {FStar_Syntax_Syntax.ppname = uu___158_26292.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___158_26292.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in (uu____26289)::out)
in ((uu____26286), (rest1)))))
end))
end
| uu____26297 -> begin
(([]), (bindings1))
end))
in (

let uu____26304 = (aux bindings)
in (match (uu____26304) with
| (closing, bindings1) -> begin
(

let uu____26329 = (FStar_Syntax_Util.close_forall_no_univs (FStar_List.rev closing) q)
in ((uu____26329), (bindings1)))
end)))
in (match (uu____26210) with
| (q1, bindings1) -> begin
(

let uu____26352 = (

let uu____26357 = (FStar_List.filter (fun uu___125_26362 -> (match (uu___125_26362) with
| FStar_TypeChecker_Env.Binding_sig (uu____26363) -> begin
false
end
| uu____26370 -> begin
true
end)) bindings1)
in (encode_env_bindings env uu____26357))
in (match (uu____26352) with
| (env_decls, env1) -> begin
((

let uu____26388 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____26388) with
| true -> begin
(

let uu____26389 = (FStar_Syntax_Print.term_to_string q1)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____26389))
end
| uu____26390 -> begin
()
end));
(

let uu____26391 = (encode_formula q1 env1)
in (match (uu____26391) with
| (phi, qdecls) -> begin
(

let uu____26412 = (

let uu____26417 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____26417 phi))
in (match (uu____26412) with
| (labels, phi1) -> begin
(

let uu____26434 = (encode_labels labels)
in (match (uu____26434) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____26471 = (

let uu____26478 = (FStar_SMTEncoding_Util.mkNot phi1)
in (

let uu____26479 = (varops.mk_unique "@query")
in ((uu____26478), (FStar_Pervasives_Native.Some ("query")), (uu____26479))))
in (FStar_SMTEncoding_Util.mkAssume uu____26471))
in (

let suffix = (FStar_List.append label_suffix ((FStar_SMTEncoding_Term.Echo ("Done!"))::[]))
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

let uu____26498 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____26498 tcenv))
in ((FStar_SMTEncoding_Z3.push "query");
(

let uu____26500 = (encode_formula q env)
in (match (uu____26500) with
| (f, uu____26506) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____26508) -> begin
true
end
| uu____26513 -> begin
false
end);
)
end));
)))






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


let vargs : 'Auu____71 'Auu____72 'Auu____73 . (('Auu____73, 'Auu____72) FStar_Util.either * 'Auu____71) Prims.list  ->  (('Auu____73, 'Auu____72) FStar_Util.either * 'Auu____71) Prims.list = (fun args -> (FStar_List.filter (fun uu___108_119 -> (match (uu___108_119) with
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

let uu___132_221 = a
in (

let uu____222 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____222; FStar_Syntax_Syntax.index = uu___132_221.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___132_221.FStar_Syntax_Syntax.sort}))
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

let uu____1025 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____1025 (fun uu____1111 -> (match (uu____1111) with
| (names1, uu____1123) -> begin
(FStar_Util.smap_try_find names1 y1)
end))))
in (match (uu____1022) with
| FStar_Pervasives_Native.None -> begin
y1
end
| FStar_Pervasives_Native.Some (uu____1132) -> begin
((FStar_Util.incr ctr);
(

let uu____1155 = (

let uu____1156 = (

let uu____1157 = (FStar_ST.op_Bang ctr)
in (Prims.string_of_int uu____1157))
in (Prims.strcat "__" uu____1156))
in (Prims.strcat y1 uu____1155));
)
end))
in (

let top_scope = (

let uu____1185 = (

let uu____1194 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1194))
in (FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1185))
in ((FStar_Util.smap_add top_scope y2 true);
y2;
)))))
in (

let new_var = (fun pp rn -> (FStar_All.pipe_left mk_unique (Prims.strcat pp.FStar_Ident.idText (Prims.strcat "__" (Prims.string_of_int rn)))))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id1 = (fun uu____1306 -> ((FStar_Util.incr ctr);
(FStar_ST.op_Bang ctr);
))
in (

let fresh1 = (fun pfx -> (

let uu____1357 = (

let uu____1358 = (next_id1 ())
in (FStar_All.pipe_left Prims.string_of_int uu____1358))
in (FStar_Util.format2 "%s_%s" pfx uu____1357)))
in (

let string_const = (fun s -> (

let uu____1363 = (

let uu____1366 = (FStar_ST.op_Bang scopes)
in (FStar_Util.find_map uu____1366 (fun uu____1452 -> (match (uu____1452) with
| (uu____1463, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____1363) with
| FStar_Pervasives_Native.Some (f) -> begin
f
end
| FStar_Pervasives_Native.None -> begin
(

let id = (next_id1 ())
in (

let f = (

let uu____1476 = (FStar_SMTEncoding_Util.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1476))
in (

let top_scope = (

let uu____1480 = (

let uu____1489 = (FStar_ST.op_Bang scopes)
in (FStar_List.hd uu____1489))
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1480))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push1 = (fun uu____1590 -> (

let uu____1591 = (

let uu____1602 = (new_scope ())
in (

let uu____1611 = (FStar_ST.op_Bang scopes)
in (uu____1602)::uu____1611))
in (FStar_ST.op_Colon_Equals scopes uu____1591)))
in (

let pop1 = (fun uu____1761 -> (

let uu____1762 = (

let uu____1773 = (FStar_ST.op_Bang scopes)
in (FStar_List.tl uu____1773))
in (FStar_ST.op_Colon_Equals scopes uu____1762)))
in (

let mark1 = (fun uu____1923 -> (push1 ()))
in (

let reset_mark1 = (fun uu____1927 -> (pop1 ()))
in (

let commit_mark1 = (fun uu____1931 -> (

let uu____1932 = (FStar_ST.op_Bang scopes)
in (match (uu____1932) with
| ((hd1, hd2))::((next1, next2))::tl1 -> begin
((FStar_Util.smap_fold hd1 (fun key value v1 -> (FStar_Util.smap_add next1 key value)) ());
(FStar_Util.smap_fold hd2 (fun key value v1 -> (FStar_Util.smap_add next2 key value)) ());
(FStar_ST.op_Colon_Equals scopes ((((next1), (next2)))::tl1));
)
end
| uu____2144 -> begin
(failwith "Impossible")
end)))
in {push = push1; pop = pop1; mark = mark1; reset_mark = reset_mark1; commit_mark = commit_mark1; new_var = new_var; new_fvar = new_fvar; fresh = fresh1; string_const = string_const; next_id = next_id1; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let uu___133_2159 = x
in (

let uu____2160 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____2160; FStar_Syntax_Syntax.index = uu___133_2159.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___133_2159.FStar_Syntax_Syntax.sort})))

type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____2194 -> begin
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
| uu____2232 -> begin
false
end))


let __proj__Binding_fvar__item___0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_0) -> begin
_0
end))


let binder_of_eithervar : 'Auu____2283 'Auu____2284 . 'Auu____2284  ->  ('Auu____2284 * 'Auu____2283 FStar_Pervasives_Native.option) = (fun v1 -> ((v1), (FStar_Pervasives_Native.None)))

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


let mk_cache_entry : 'Auu____2598 . 'Auu____2598  ->  Prims.string  ->  FStar_SMTEncoding_Term.sort Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  cache_entry = (fun env tsym cvar_sorts t_decls -> (

let names1 = (FStar_All.pipe_right t_decls (FStar_List.collect (fun uu___109_2632 -> (match (uu___109_2632) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(a.FStar_SMTEncoding_Term.assumption_name)::[]
end
| uu____2636 -> begin
[]
end))))
in {cache_symbol_name = tsym; cache_symbol_arg_sorts = cvar_sorts; cache_symbol_decls = t_decls; cache_symbol_assumption_names = names1}))


let use_cache_entry : cache_entry  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun ce -> (FStar_SMTEncoding_Term.RetainAssumptions (ce.cache_symbol_assumption_names))::[])


let print_env : env_t  ->  Prims.string = (fun e -> (

let uu____2647 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun uu___110_2657 -> (match (uu___110_2657) with
| Binding_var (x, uu____2659) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, uu____2661, uu____2662, uu____2663) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right uu____2647 (FStar_String.concat ", "))))


let lookup_binding : 'Auu____2680 . env_t  ->  (binding  ->  'Auu____2680 FStar_Pervasives_Native.option)  ->  'Auu____2680 FStar_Pervasives_Native.option = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string FStar_Pervasives_Native.option = (fun env t -> (

let uu____2710 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____2710) with
| true -> begin
(

let uu____2713 = (FStar_Syntax_Print.term_to_string t)
in FStar_Pervasives_Native.Some (uu____2713))
end
| uu____2714 -> begin
FStar_Pervasives_Native.None
end)))


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (

let uu____2728 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (uu____2728)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (Prims.strcat "@x" (Prims.string_of_int env.depth))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let uu___134_2746 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___134_2746.tcenv; warn = uu___134_2746.warn; cache = uu___134_2746.cache; nolabels = uu___134_2746.nolabels; use_zfuel_name = uu___134_2746.use_zfuel_name; encode_non_total_function_typ = uu___134_2746.encode_non_total_function_typ; current_module_name = uu___134_2746.current_module_name}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___135_2766 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___135_2766.depth; tcenv = uu___135_2766.tcenv; warn = uu___135_2766.warn; cache = uu___135_2766.cache; nolabels = uu___135_2766.nolabels; use_zfuel_name = uu___135_2766.use_zfuel_name; encode_non_total_function_typ = uu___135_2766.encode_non_total_function_typ; current_module_name = uu___135_2766.current_module_name}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___136_2790 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___136_2790.depth; tcenv = uu___136_2790.tcenv; warn = uu___136_2790.warn; cache = uu___136_2790.cache; nolabels = uu___136_2790.nolabels; use_zfuel_name = uu___136_2790.use_zfuel_name; encode_non_total_function_typ = uu___136_2790.encode_non_total_function_typ; current_module_name = uu___136_2790.current_module_name}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___137_2803 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = uu___137_2803.depth; tcenv = uu___137_2803.tcenv; warn = uu___137_2803.warn; cache = uu___137_2803.cache; nolabels = uu___137_2803.nolabels; use_zfuel_name = uu___137_2803.use_zfuel_name; encode_non_total_function_typ = uu___137_2803.encode_non_total_function_typ; current_module_name = uu___137_2803.current_module_name}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun uu___111_2829 -> (match (uu___111_2829) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
FStar_Pervasives_Native.Some (((b), (t)))
end
| uu____2842 -> begin
FStar_Pervasives_Native.None
end))))
in (

let uu____2847 = (aux a)
in (match (uu____2847) with
| FStar_Pervasives_Native.None -> begin
(

let a2 = (unmangle a)
in (

let uu____2859 = (aux a2)
in (match (uu____2859) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2870 = (

let uu____2871 = (FStar_Syntax_Print.bv_to_string a2)
in (

let uu____2872 = (print_env env)
in (FStar_Util.format2 "Bound term variable not found (after unmangling): %s in environment: %s" uu____2871 uu____2872)))
in (failwith uu____2870))
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

let uu____2901 = (

let uu___138_2902 = env
in (

let uu____2903 = (

let uu____2906 = (

let uu____2907 = (

let uu____2920 = (

let uu____2923 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)) uu____2923))
in ((x), (fname), (uu____2920), (FStar_Pervasives_Native.None)))
in Binding_fvar (uu____2907))
in (uu____2906)::env.bindings)
in {bindings = uu____2903; depth = uu___138_2902.depth; tcenv = uu___138_2902.tcenv; warn = uu___138_2902.warn; cache = uu___138_2902.cache; nolabels = uu___138_2902.nolabels; use_zfuel_name = uu___138_2902.use_zfuel_name; encode_non_total_function_typ = uu___138_2902.encode_non_total_function_typ; current_module_name = uu___138_2902.current_module_name}))
in ((fname), (ftok), (uu____2901))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) FStar_Pervasives_Native.option = (fun env a -> (lookup_binding env (fun uu___112_2967 -> (match (uu___112_2967) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
FStar_Pervasives_Native.Some (((t1), (t2), (t3)))
end
| uu____3006 -> begin
FStar_Pervasives_Native.None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (

let uu____3025 = (lookup_binding env (fun uu___113_3033 -> (match (uu___113_3033) with
| Binding_fvar (b, t1, t2, t3) when (Prims.op_Equality b.FStar_Ident.str s) -> begin
FStar_Pervasives_Native.Some (())
end
| uu____3048 -> begin
FStar_Pervasives_Native.None
end)))
in (FStar_All.pipe_right uu____3025 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option * FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option) = (fun env a -> (

let uu____3069 = (try_lookup_lid env a)
in (match (uu____3069) with
| FStar_Pervasives_Native.None -> begin
(

let uu____3102 = (

let uu____3103 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____3103))
in (failwith uu____3102))
end
| FStar_Pervasives_Native.Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  env_t = (fun env x fname ftok -> (

let uu___139_3155 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (FStar_Pervasives_Native.None))))::env.bindings; depth = uu___139_3155.depth; tcenv = uu___139_3155.tcenv; warn = uu___139_3155.warn; cache = uu___139_3155.cache; nolabels = uu___139_3155.nolabels; use_zfuel_name = uu___139_3155.use_zfuel_name; encode_non_total_function_typ = uu___139_3155.encode_non_total_function_typ; current_module_name = uu___139_3155.current_module_name}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let uu____3172 = (lookup_lid env x)
in (match (uu____3172) with
| (t1, t2, uu____3185) -> begin
(

let t3 = (

let uu____3195 = (

let uu____3202 = (

let uu____3205 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____3205)::[])
in ((f), (uu____3202)))
in (FStar_SMTEncoding_Util.mkApp uu____3195))
in (

let uu___140_3210 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (FStar_Pervasives_Native.Some (t3)))))::env.bindings; depth = uu___140_3210.depth; tcenv = uu___140_3210.tcenv; warn = uu___140_3210.warn; cache = uu___140_3210.cache; nolabels = uu___140_3210.nolabels; use_zfuel_name = uu___140_3210.use_zfuel_name; encode_non_total_function_typ = uu___140_3210.encode_non_total_function_typ; current_module_name = uu___140_3210.current_module_name}))
end)))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env l -> (

let uu____3225 = (try_lookup_lid env l)
in (match (uu____3225) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| FStar_Pervasives_Native.Some (f) when env.use_zfuel_name -> begin
FStar_Pervasives_Native.Some (f)
end
| uu____3274 -> begin
(match (sym) with
| FStar_Pervasives_Native.Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____3282, (fuel)::[]) -> begin
(

let uu____3286 = (

let uu____3287 = (

let uu____3288 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____3288 FStar_Pervasives_Native.fst))
in (FStar_Util.starts_with uu____3287 "fuel"))
in (match (uu____3286) with
| true -> begin
(

let uu____3291 = (

let uu____3292 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____3292 fuel))
in (FStar_All.pipe_left (fun _0_42 -> FStar_Pervasives_Native.Some (_0_42)) uu____3291))
end
| uu____3295 -> begin
FStar_Pervasives_Native.Some (t)
end))
end
| uu____3296 -> begin
FStar_Pervasives_Native.Some (t)
end)
end
| uu____3297 -> begin
FStar_Pervasives_Native.None
end)
end)
end)))


let lookup_free_var : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let uu____3312 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____3312) with
| FStar_Pervasives_Native.Some (t) -> begin
t
end
| FStar_Pervasives_Native.None -> begin
(

let uu____3316 = (

let uu____3317 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____3317))
in (failwith uu____3316))
end)))


let lookup_free_var_name : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  Prims.string = (fun env a -> (

let uu____3330 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____3330) with
| (x, uu____3342, uu____3343) -> begin
x
end)))


let lookup_free_var_sym : env_t  ->  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t  ->  (FStar_SMTEncoding_Term.op * FStar_SMTEncoding_Term.term Prims.list) = (fun env a -> (

let uu____3370 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____3370) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| FStar_Pervasives_Native.Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____3406; FStar_SMTEncoding_Term.rng = uu____3407}) when env.use_zfuel_name -> begin
((g), (zf))
end
| uu____3422 -> begin
(match (sym) with
| FStar_Pervasives_Native.None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| FStar_Pervasives_Native.Some (sym1) -> begin
(match (sym1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| uu____3446 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___114_3464 -> (match (uu___114_3464) with
| Binding_fvar (uu____3467, nm', tok, uu____3470) when (Prims.op_Equality nm nm') -> begin
tok
end
| uu____3479 -> begin
FStar_Pervasives_Native.None
end))))


let mkForall_fuel' : 'Auu____3486 . 'Auu____3486  ->  (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (fun n1 uu____3504 -> (match (uu____3504) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____3529 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____3534 = (FStar_Options.unthrottle_inductives ())
in (match (uu____3534) with
| true -> begin
(fallback ())
end
| uu____3535 -> begin
(

let uu____3536 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____3536) with
| (fsym, fterm) -> begin
(

let add_fuel1 = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____3567 -> begin
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

let uu____3588 = (add_fuel1 guards)
in (FStar_SMTEncoding_Util.mk_and_l uu____3588))
end
| uu____3591 -> begin
(

let uu____3592 = (add_fuel1 ((guard)::[]))
in (FStar_All.pipe_right uu____3592 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard1), (body'))))
end
| uu____3597 -> begin
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
| FStar_Syntax_Syntax.Tm_arrow (uu____3641) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____3654) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____3661) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uvar (uu____3662) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____3679) -> begin
true
end
| FStar_Syntax_Syntax.Tm_constant (uu____3696) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3698 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3698 FStar_Option.isNone))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____3716; FStar_Syntax_Syntax.vars = uu____3717}, uu____3718) -> begin
(

let uu____3739 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3739 FStar_Option.isNone))
end
| uu____3756 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____3765 = (

let uu____3766 = (FStar_Syntax_Util.un_uinst t)
in uu____3766.FStar_Syntax_Syntax.n)
in (match (uu____3765) with
| FStar_Syntax_Syntax.Tm_abs (uu____3769, uu____3770, FStar_Pervasives_Native.Some (rc)) -> begin
(((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___115_3791 -> (match (uu___115_3791) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____3792 -> begin
false
end)) rc.FStar_Syntax_Syntax.residual_flags))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____3794 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3794 FStar_Option.isSome))
end
| uu____3811 -> begin
false
end)))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____3820 = (head_normal env t)
in (match (uu____3820) with
| true -> begin
t
end
| uu____3821 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____3834 = (

let uu____3835 = (FStar_Syntax_Syntax.null_binder t)
in (uu____3835)::[])
in (

let uu____3836 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.abs uu____3834 uu____3836 FStar_Pervasives_Native.None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((FStar_Pervasives_Native.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(

let uu____3876 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out uu____3876))
end
| s -> begin
(

let uu____3881 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out uu____3881))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___116_3899 -> (match (uu___116_3899) with
| FStar_SMTEncoding_Term.Var ("ApplyTT") -> begin
true
end
| FStar_SMTEncoding_Term.Var ("ApplyTF") -> begin
true
end
| uu____3900 -> begin
false
end))


let is_an_eta_expansion : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env vars body -> (

let rec check_partial_applications = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____3939; FStar_SMTEncoding_Term.rng = uu____3940})::[]), (x)::xs1) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(check_partial_applications f xs1)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____3963) -> begin
(

let uu____3972 = ((Prims.op_Equality (FStar_List.length args) (FStar_List.length xs)) && (FStar_List.forall2 (fun a v1 -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v1)
end
| uu____3983 -> begin
false
end)) args (FStar_List.rev xs)))
in (match (uu____3972) with
| true -> begin
(tok_of_name env f)
end
| uu____3986 -> begin
FStar_Pervasives_Native.None
end))
end
| (uu____3987, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____3991 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (

let uu____3995 = (FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)
in (not (uu____3995))))))
in (match (uu____3991) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____3998 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____3999 -> begin
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
| uu____4229 -> begin
false
end))

exception Inner_let_rec


let uu___is_Inner_let_rec : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inner_let_rec -> begin
true
end
| uu____4234 -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun uu___117_4238 -> (match (uu___117_4238) with
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

let uu____4240 = (

let uu____4247 = (

let uu____4250 = (

let uu____4251 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt uu____4251))
in (uu____4250)::[])
in (("FStar.Char.Char"), (uu____4247)))
in (FStar_SMTEncoding_Util.mkApp uu____4240))
end
| FStar_Const.Const_int (i, FStar_Pervasives_Native.None) -> begin
(

let uu____4265 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____4265))
end
| FStar_Const.Const_int (i, FStar_Pervasives_Native.Some (uu____4267)) -> begin
(failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (s, uu____4283) -> begin
(varops.string_const s)
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(

let uu____4286 = (

let uu____4287 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" uu____4287))
in (failwith uu____4286))
end))


let as_function_typ : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____4308) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_refine (uu____4321) -> begin
(

let uu____4328 = (FStar_Syntax_Util.unrefine t1)
in (aux true uu____4328))
end
| uu____4329 -> begin
(match (norm1) with
| true -> begin
(

let uu____4330 = (whnf env t1)
in (aux false uu____4330))
end
| uu____4331 -> begin
(

let uu____4332 = (

let uu____4333 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____4334 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____4333 uu____4334)))
in (failwith uu____4332))
end)
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| uu____4366 -> begin
(

let uu____4367 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____4367)))
end)))


let is_arithmetic_primitive : 'Auu____4384 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____4384 Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4404)::(uu____4405)::[]) -> begin
(((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Subtraction)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____4409)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus)
end
| uu____4412 -> begin
false
end))


let isInteger : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
true
end
| uu____4434 -> begin
false
end))


let getInteger : FStar_Syntax_Syntax.term'  ->  Prims.int = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
(FStar_Util.int_of_string n1)
end
| uu____4450 -> begin
(failwith "Expected an Integer term")
end))


let is_BitVector_primitive : 'Auu____4457 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____4457) Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____4496))::(uu____4497)::(uu____4498)::[]) -> begin
((((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_and_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_xor_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_left_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_right_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_udiv_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mod_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____4549))::(uu____4550)::[]) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_to_nat_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| uu____4587 -> begin
false
end))


let rec encode_binders : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____4796 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4796) with
| true -> begin
(

let uu____4797 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____4797))
end
| uu____4798 -> begin
()
end));
(

let uu____4799 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____4883 b -> (match (uu____4883) with
| (vars, guards, env1, decls, names1) -> begin
(

let uu____4962 = (

let x = (unmangle (FStar_Pervasives_Native.fst b))
in (

let uu____4978 = (gen_term_var env1 x)
in (match (uu____4978) with
| (xxsym, xx, env') -> begin
(

let uu____5002 = (

let uu____5007 = (norm env1 x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____5007 env1 xx))
in (match (uu____5002) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____4962) with
| (v1, g, env2, decls', n1) -> begin
(((v1)::vars), ((g)::guards), (env2), ((FStar_List.append decls decls')), ((n1)::names1))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____4799) with
| (vars, guards, env1, decls, names1) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env1), (decls), ((FStar_List.rev names1)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____5166 = (encode_term t env)
in (match (uu____5166) with
| (t1, decls) -> begin
(

let uu____5177 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1)
in ((uu____5177), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____5188 = (encode_term t env)
in (match (uu____5188) with
| (t1, decls) -> begin
(match (fuel_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5203 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t1)
in ((uu____5203), (decls)))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____5205 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1)
in ((uu____5205), (decls)))
end)
end)))
and encode_arith_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.args  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun env head1 args_e -> (

let uu____5211 = (encode_args args_e env)
in (match (uu____5211) with
| (arg_tms, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____5230 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms1 -> (

let uu____5239 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____5239)))
in (

let binary = (fun arg_tms1 -> (

let uu____5252 = (

let uu____5253 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____5253))
in (

let uu____5254 = (

let uu____5255 = (

let uu____5256 = (FStar_List.tl arg_tms1)
in (FStar_List.hd uu____5256))
in (FStar_SMTEncoding_Term.unboxInt uu____5255))
in ((uu____5252), (uu____5254)))))
in (

let mk_default = (fun uu____5262 -> (

let uu____5263 = (lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____5263) with
| (fname, fuel_args) -> begin
(FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args arg_tms))))
end)))
in (

let mk_l = (fun op mk_args ts -> (

let uu____5314 = (FStar_Options.smtencoding_l_arith_native ())
in (match (uu____5314) with
| true -> begin
(

let uu____5315 = (

let uu____5316 = (mk_args ts)
in (op uu____5316))
in (FStar_All.pipe_right uu____5315 FStar_SMTEncoding_Term.boxInt))
end
| uu____5317 -> begin
(mk_default ())
end)))
in (

let mk_nl = (fun nm op ts -> (

let uu____5345 = (FStar_Options.smtencoding_nl_arith_wrapped ())
in (match (uu____5345) with
| true -> begin
(

let uu____5346 = (binary ts)
in (match (uu____5346) with
| (t1, t2) -> begin
(

let uu____5353 = (FStar_SMTEncoding_Util.mkApp ((nm), ((t1)::(t2)::[])))
in (FStar_All.pipe_right uu____5353 FStar_SMTEncoding_Term.boxInt))
end))
end
| uu____5356 -> begin
(

let uu____5357 = (FStar_Options.smtencoding_nl_arith_native ())
in (match (uu____5357) with
| true -> begin
(

let uu____5358 = (op (binary ts))
in (FStar_All.pipe_right uu____5358 FStar_SMTEncoding_Term.boxInt))
end
| uu____5359 -> begin
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

let uu____5489 = (

let uu____5498 = (FStar_List.tryFind (fun uu____5520 -> (match (uu____5520) with
| (l, uu____5530) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____5498 FStar_Util.must))
in (match (uu____5489) with
| (uu____5569, op) -> begin
(

let uu____5579 = (op arg_tms)
in ((uu____5579), (decls)))
end)))))))))))))))
end)))
and encode_BitVector_term : env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.arg Prims.list  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun env head1 args_e -> (

let uu____5587 = (FStar_List.hd args_e)
in (match (uu____5587) with
| (tm_sz, uu____5595) -> begin
(

let sz = (getInteger tm_sz.FStar_Syntax_Syntax.n)
in (

let sz_key = (FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz))
in (

let sz_decls = (

let uu____5605 = (FStar_Util.smap_try_find env.cache sz_key)
in (match (uu____5605) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
[]
end
| FStar_Pervasives_Native.None -> begin
(

let t_decls = (FStar_SMTEncoding_Term.mkBvConstructor sz)
in ((

let uu____5613 = (mk_cache_entry env "" [] [])
in (FStar_Util.smap_add env.cache sz_key uu____5613));
t_decls;
))
end))
in (

let uu____5614 = (match (((head1.FStar_Syntax_Syntax.n), (args_e))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5634)::((sz_arg, uu____5636))::(uu____5637)::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) && (isInteger sz_arg.FStar_Syntax_Syntax.n)) -> begin
(

let uu____5686 = (

let uu____5689 = (FStar_List.tail args_e)
in (FStar_List.tail uu____5689))
in (

let uu____5692 = (

let uu____5695 = (getInteger sz_arg.FStar_Syntax_Syntax.n)
in FStar_Pervasives_Native.Some (uu____5695))
in ((uu____5686), (uu____5692))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5701)::((sz_arg, uu____5703))::(uu____5704)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) -> begin
(

let uu____5753 = (

let uu____5754 = (FStar_Syntax_Print.term_to_string sz_arg)
in (FStar_Util.format1 "Not a constant bitvector extend size: %s" uu____5754))
in (failwith uu____5753))
end
| uu____5763 -> begin
(

let uu____5770 = (FStar_List.tail args_e)
in ((uu____5770), (FStar_Pervasives_Native.None)))
end)
in (match (uu____5614) with
| (arg_tms, ext_sz) -> begin
(

let uu____5793 = (encode_args arg_tms env)
in (match (uu____5793) with
| (arg_tms1, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____5814 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms2 -> (

let uu____5823 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5823)))
in (

let unary_arith = (fun arg_tms2 -> (

let uu____5832 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxInt uu____5832)))
in (

let binary = (fun arg_tms2 -> (

let uu____5845 = (

let uu____5846 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5846))
in (

let uu____5847 = (

let uu____5848 = (

let uu____5849 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____5849))
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5848))
in ((uu____5845), (uu____5847)))))
in (

let binary_arith = (fun arg_tms2 -> (

let uu____5864 = (

let uu____5865 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____5865))
in (

let uu____5866 = (

let uu____5867 = (

let uu____5868 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____5868))
in (FStar_SMTEncoding_Term.unboxInt uu____5867))
in ((uu____5864), (uu____5866)))))
in (

let mk_bv = (fun op mk_args resBox ts -> (

let uu____5917 = (

let uu____5918 = (mk_args ts)
in (op uu____5918))
in (FStar_All.pipe_right uu____5917 resBox)))
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

let uu____6008 = (

let uu____6011 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (FStar_SMTEncoding_Util.mkBvUext uu____6011))
in (

let uu____6013 = (

let uu____6016 = (

let uu____6017 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (sz + uu____6017))
in (FStar_SMTEncoding_Term.boxBitVec uu____6016))
in (mk_bv uu____6008 unary uu____6013 arg_tms2))))
in (

let to_int = (mk_bv FStar_SMTEncoding_Util.mkBvToNat unary FStar_SMTEncoding_Term.boxInt)
in (

let bv_to = (mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz) unary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let ops = (((FStar_Parser_Const.bv_and_lid), (bv_and)))::(((FStar_Parser_Const.bv_xor_lid), (bv_xor)))::(((FStar_Parser_Const.bv_or_lid), (bv_or)))::(((FStar_Parser_Const.bv_shift_left_lid), (bv_shl)))::(((FStar_Parser_Const.bv_shift_right_lid), (bv_shr)))::(((FStar_Parser_Const.bv_udiv_lid), (bv_udiv)))::(((FStar_Parser_Const.bv_mod_lid), (bv_mod)))::(((FStar_Parser_Const.bv_mul_lid), (bv_mul)))::(((FStar_Parser_Const.bv_ult_lid), (bv_ult)))::(((FStar_Parser_Const.bv_uext_lid), (bv_uext)))::(((FStar_Parser_Const.bv_to_nat_lid), (to_int)))::(((FStar_Parser_Const.nat_to_bv_lid), (bv_to)))::[]
in (

let uu____6192 = (

let uu____6201 = (FStar_List.tryFind (fun uu____6223 -> (match (uu____6223) with
| (l, uu____6233) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____6201 FStar_Util.must))
in (match (uu____6192) with
| (uu____6274, op) -> begin
(

let uu____6284 = (op arg_tms1)
in ((uu____6284), ((FStar_List.append sz_decls decls))))
end)))))))))))))))))))))
end))
end)))))
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____6295 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____6295) with
| true -> begin
(

let uu____6296 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____6297 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6298 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____6296 uu____6297 uu____6298))))
end
| uu____6299 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____6304) -> begin
(

let uu____6329 = (

let uu____6330 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____6331 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6332 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____6333 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6330 uu____6331 uu____6332 uu____6333)))))
in (failwith uu____6329))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____6338 = (

let uu____6339 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____6340 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____6341 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____6342 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6339 uu____6340 uu____6341 uu____6342)))))
in (failwith uu____6338))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____6348 = (

let uu____6349 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____6349))
in (failwith uu____6348))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, k, uu____6356) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____6398) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t1 = (lookup_term_var env x)
in ((t1), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v1) -> begin
(

let uu____6408 = (lookup_free_var env v1.FStar_Syntax_Syntax.fv_name)
in ((uu____6408), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____6411) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____6415) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____6421 = (encode_const c)
in ((uu____6421), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let module_name = env.current_module_name
in (

let uu____6443 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____6443) with
| (binders1, res) -> begin
(

let uu____6454 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____6454) with
| true -> begin
(

let uu____6459 = (encode_binders FStar_Pervasives_Native.None binders1 env)
in (match (uu____6459) with
| (vars, guards, env', decls, uu____6484) -> begin
(

let fsym = (

let uu____6502 = (varops.fresh "f")
in ((uu____6502), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____6505 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___141_6514 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___141_6514.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___141_6514.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___141_6514.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___141_6514.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___141_6514.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___141_6514.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___141_6514.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___141_6514.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___141_6514.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___141_6514.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___141_6514.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___141_6514.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___141_6514.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___141_6514.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___141_6514.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___141_6514.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___141_6514.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___141_6514.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___141_6514.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___141_6514.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___141_6514.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___141_6514.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___141_6514.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___141_6514.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___141_6514.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___141_6514.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___141_6514.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___141_6514.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___141_6514.FStar_TypeChecker_Env.identifier_info}) res)
in (match (uu____6505) with
| (pre_opt, res_t) -> begin
(

let uu____6525 = (encode_term_pred FStar_Pervasives_Native.None res_t env' app)
in (match (uu____6525) with
| (res_pred, decls') -> begin
(

let uu____6536 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6549 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____6549), ([])))
end
| FStar_Pervasives_Native.Some (pre) -> begin
(

let uu____6553 = (encode_formula pre env')
in (match (uu____6553) with
| (guard, decls0) -> begin
(

let uu____6566 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____6566), (decls0)))
end))
end)
in (match (uu____6536) with
| (guards1, guard_decls) -> begin
(

let t_interp = (

let uu____6578 = (

let uu____6589 = (FStar_SMTEncoding_Util.mkImp ((guards1), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____6589)))
in (FStar_SMTEncoding_Util.mkForall uu____6578))
in (

let cvars = (

let uu____6607 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____6607 (FStar_List.filter (fun uu____6621 -> (match (uu____6621) with
| (x, uu____6627) -> begin
(Prims.op_disEquality x (FStar_Pervasives_Native.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____6646 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____6646) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____6654 = (

let uu____6655 = (

let uu____6662 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____6662)))
in (FStar_SMTEncoding_Util.mkApp uu____6655))
in ((uu____6654), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append guard_decls (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let tsym = (

let uu____6682 = (

let uu____6683 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____6683))
in (varops.mk_unique uu____6682))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars)
in (

let caption = (

let uu____6694 = (FStar_Options.log_queries ())
in (match (uu____6694) with
| true -> begin
(

let uu____6697 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in FStar_Pervasives_Native.Some (uu____6697))
end
| uu____6698 -> begin
FStar_Pervasives_Native.None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t1 = (

let uu____6705 = (

let uu____6712 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____6712)))
in (FStar_SMTEncoding_Util.mkApp uu____6705))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = (Prims.strcat "kinding_" tsym)
in (

let uu____6724 = (

let uu____6731 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____6731), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____6724)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t1)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t1)
in (

let pre_typing = (

let a_name = (Prims.strcat "pre_typing_" tsym)
in (

let uu____6752 = (

let uu____6759 = (

let uu____6760 = (

let uu____6771 = (

let uu____6772 = (

let uu____6777 = (

let uu____6778 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____6778))
in ((f_has_t), (uu____6777)))
in (FStar_SMTEncoding_Util.mkImp uu____6772))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____6771)))
in (mkForall_fuel uu____6760))
in ((uu____6759), (FStar_Pervasives_Native.Some ("pre-typing for functions")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6752)))
in (

let t_interp1 = (

let a_name = (Prims.strcat "interpretation_" tsym)
in (

let uu____6801 = (

let uu____6808 = (

let uu____6809 = (

let uu____6820 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____6820)))
in (FStar_SMTEncoding_Util.mkForall uu____6809))
in ((uu____6808), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6801)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp1)::[]))))
in ((

let uu____6845 = (mk_cache_entry env tsym cvar_sorts t_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____6845));
((t1), (t_decls));
)))))))))))))
end))))))
end))
end))
end)))))
end))
end
| uu____6848 -> begin
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

let uu____6860 = (

let uu____6867 = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____6867), (FStar_Pervasives_Native.Some ("Typing for non-total arrows")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6860)))
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

let uu____6879 = (

let uu____6886 = (

let uu____6887 = (

let uu____6898 = (

let uu____6899 = (

let uu____6904 = (

let uu____6905 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____6905))
in ((f_has_t), (uu____6904)))
in (FStar_SMTEncoding_Util.mkImp uu____6899))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____6898)))
in (mkForall_fuel uu____6887))
in ((uu____6886), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____6879)))
in ((t1), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____6932) -> begin
(

let uu____6939 = (

let uu____6944 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____6944) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.pos = uu____6951; FStar_Syntax_Syntax.vars = uu____6952} -> begin
(

let uu____6959 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____6959) with
| (b, f1) -> begin
(

let uu____6984 = (

let uu____6985 = (FStar_List.hd b)
in (FStar_Pervasives_Native.fst uu____6985))
in ((uu____6984), (f1)))
end))
end
| uu____6994 -> begin
(failwith "impossible")
end))
in (match (uu____6939) with
| (x, f) -> begin
(

let uu____7005 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____7005) with
| (base_t, decls) -> begin
(

let uu____7016 = (gen_term_var env x)
in (match (uu____7016) with
| (x1, xtm, env') -> begin
(

let uu____7030 = (encode_formula f env')
in (match (uu____7030) with
| (refinement, decls') -> begin
(

let uu____7041 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____7041) with
| (fsym, fterm) -> begin
(

let tm_has_type_with_fuel = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (fterm)) xtm base_t)
in (

let encoding = (FStar_SMTEncoding_Util.mkAnd ((tm_has_type_with_fuel), (refinement)))
in (

let cvars = (

let uu____7057 = (

let uu____7060 = (FStar_SMTEncoding_Term.free_variables refinement)
in (

let uu____7067 = (FStar_SMTEncoding_Term.free_variables tm_has_type_with_fuel)
in (FStar_List.append uu____7060 uu____7067)))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____7057))
in (

let cvars1 = (FStar_All.pipe_right cvars (FStar_List.filter (fun uu____7100 -> (match (uu____7100) with
| (y, uu____7106) -> begin
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

let uu____7139 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____7139) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____7147 = (

let uu____7148 = (

let uu____7155 = (FStar_All.pipe_right cvars1 (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.cache_symbol_name), (uu____7155)))
in (FStar_SMTEncoding_Util.mkApp uu____7148))
in ((uu____7147), ((FStar_List.append decls (FStar_List.append decls' (use_cache_entry cache_entry))))))
end
| FStar_Pervasives_Native.None -> begin
(

let module_name = env.current_module_name
in (

let tsym = (

let uu____7176 = (

let uu____7177 = (

let uu____7178 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "_Tm_refine_" uu____7178))
in (Prims.strcat module_name uu____7177))
in (varops.mk_unique uu____7176))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars1)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let t1 = (

let uu____7192 = (

let uu____7199 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((tsym), (uu____7199)))
in (FStar_SMTEncoding_Util.mkApp uu____7192))
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

let uu____7214 = (

let uu____7221 = (

let uu____7222 = (

let uu____7233 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars1), (uu____7233)))
in (FStar_SMTEncoding_Util.mkForall uu____7222))
in ((uu____7221), (FStar_Pervasives_Native.Some ((Prims.strcat "haseq for " tsym))), ((Prims.strcat "haseq" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____7214))
in (

let t_valid = (

let xx = ((x1), (FStar_SMTEncoding_Term.Term_sort))
in (

let valid_t = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((t1)::[])))
in (

let uu____7259 = (

let uu____7266 = (

let uu____7267 = (

let uu____7278 = (

let uu____7279 = (

let uu____7284 = (

let uu____7285 = (

let uu____7296 = (FStar_SMTEncoding_Util.mkAnd ((x_has_base_t), (refinement)))
in (([]), ((xx)::[]), (uu____7296)))
in (FStar_SMTEncoding_Util.mkExists uu____7285))
in ((uu____7284), (valid_t)))
in (FStar_SMTEncoding_Util.mkIff uu____7279))
in ((((valid_t)::[])::[]), (cvars1), (uu____7278)))
in (FStar_SMTEncoding_Util.mkForall uu____7267))
in ((uu____7266), (FStar_Pervasives_Native.Some ("validity axiom for refinement")), ((Prims.strcat "ref_valid_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____7259))))
in (

let t_kinding = (

let uu____7334 = (

let uu____7341 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars1), (t_has_kind)))
in ((uu____7341), (FStar_Pervasives_Native.Some ("refinement kinding")), ((Prims.strcat "refinement_kinding_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____7334))
in (

let t_interp = (

let uu____7359 = (

let uu____7366 = (

let uu____7367 = (

let uu____7378 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars1), (uu____7378)))
in (FStar_SMTEncoding_Util.mkForall uu____7367))
in (

let uu____7401 = (

let uu____7404 = (FStar_Syntax_Print.term_to_string t0)
in FStar_Pervasives_Native.Some (uu____7404))
in ((uu____7366), (uu____7401), ((Prims.strcat "refinement_interpretation_" tsym)))))
in (FStar_SMTEncoding_Util.mkAssume uu____7359))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_valid)::(t_interp)::(t_haseq1)::[])))
in ((

let uu____7411 = (mk_cache_entry env tsym cvar_sorts t_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____7411));
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

let uu____7441 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____7441))
in (

let uu____7442 = (encode_term_pred FStar_Pervasives_Native.None k env ttm)
in (match (uu____7442) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____7454 = (

let uu____7461 = (

let uu____7462 = (

let uu____7463 = (

let uu____7464 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____7464))
in (FStar_Util.format1 "uvar_typing_%s" uu____7463))
in (varops.mk_unique uu____7462))
in ((t_has_k), (FStar_Pervasives_Native.Some ("Uvar typing")), (uu____7461)))
in (FStar_SMTEncoding_Util.mkAssume uu____7454))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____7469) -> begin
(

let uu____7484 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____7484) with
| (head1, args_e) -> begin
(

let uu____7525 = (

let uu____7538 = (

let uu____7539 = (FStar_Syntax_Subst.compress head1)
in uu____7539.FStar_Syntax_Syntax.n)
in ((uu____7538), (args_e)))
in (match (uu____7525) with
| uu____7554 when (head_redex env head1) -> begin
(

let uu____7567 = (whnf env t)
in (encode_term uu____7567 env))
end
| uu____7568 when (is_arithmetic_primitive head1 args_e) -> begin
(encode_arith_term env head1 args_e)
end
| uu____7587 when (is_BitVector_primitive head1 args_e) -> begin
(encode_BitVector_term env head1 args_e)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7601; FStar_Syntax_Syntax.vars = uu____7602}, uu____7603), (uu____7604)::((v1, uu____7606))::((v2, uu____7608))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7659 = (encode_term v1 env)
in (match (uu____7659) with
| (v11, decls1) -> begin
(

let uu____7670 = (encode_term v2 env)
in (match (uu____7670) with
| (v21, decls2) -> begin
(

let uu____7681 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7681), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____7685)::((v1, uu____7687))::((v2, uu____7689))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____7736 = (encode_term v1 env)
in (match (uu____7736) with
| (v11, decls1) -> begin
(

let uu____7747 = (encode_term v2 env)
in (match (uu____7747) with
| (v21, decls2) -> begin
(

let uu____7758 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____7758), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____7761) -> begin
(

let e0 = (

let uu____7779 = (FStar_List.hd args_e)
in (FStar_TypeChecker_Util.reify_body_with_arg env.tcenv head1 uu____7779))
in ((

let uu____7787 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____7787) with
| true -> begin
(

let uu____7788 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" uu____7788))
end
| uu____7789 -> begin
()
end));
(

let e = (

let uu____7793 = (

let uu____7794 = (FStar_TypeChecker_Util.remove_reify e0)
in (

let uu____7795 = (FStar_List.tl args_e)
in (FStar_Syntax_Syntax.mk_Tm_app uu____7794 uu____7795)))
in (uu____7793 FStar_Pervasives_Native.None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____7804)), ((arg, uu____7806))::[]) -> begin
(encode_term arg env)
end
| uu____7831 -> begin
(

let uu____7844 = (encode_args args_e env)
in (match (uu____7844) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____7899 = (encode_term head1 env)
in (match (uu____7899) with
| (head2, decls') -> begin
(

let app_tm = (mk_Apply_args head2 args)
in (match (ht_opt) with
| FStar_Pervasives_Native.None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| FStar_Pervasives_Native.Some (formals, c) -> begin
(

let uu____7963 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____7963) with
| (formals1, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____8041 uu____8042 -> (match (((uu____8041), (uu____8042))) with
| ((bv, uu____8064), (a, uu____8066)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals1 args_e)
in (

let ty = (

let uu____8084 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____8084 (FStar_Syntax_Subst.subst subst1)))
in (

let uu____8089 = (encode_term_pred FStar_Pervasives_Native.None ty env app_tm)
in (match (uu____8089) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____8104 = (

let uu____8111 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____8120 = (

let uu____8121 = (

let uu____8122 = (

let uu____8123 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____8123))
in (Prims.strcat "partial_app_typing_" uu____8122))
in (varops.mk_unique uu____8121))
in ((uu____8111), (FStar_Pervasives_Native.Some ("Partial app typing")), (uu____8120))))
in (FStar_SMTEncoding_Util.mkAssume uu____8104))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____8140 = (lookup_free_var_sym env fv)
in (match (uu____8140) with
| (fname, fuel_args) -> begin
(

let tm = (FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args args))))
in ((tm), (decls)))
end)))
in (

let head2 = (FStar_Syntax_Subst.compress head1)
in (

let head_type = (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.pos = uu____8171; FStar_Syntax_Syntax.vars = uu____8172}, uu____8173) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8184; FStar_Syntax_Syntax.vars = uu____8185}, uu____8186) -> begin
(

let uu____8191 = (

let uu____8192 = (

let uu____8197 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____8197 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____8192 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____8191))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____8227 = (

let uu____8228 = (

let uu____8233 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____8233 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____8228 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____8227))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____8262, (FStar_Util.Inl (t1), uu____8264), uu____8265) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____8314, (FStar_Util.Inr (c), uu____8316), uu____8317) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| uu____8366 -> begin
FStar_Pervasives_Native.None
end)
in (match (head_type) with
| FStar_Pervasives_Native.None -> begin
(encode_partial_app FStar_Pervasives_Native.None)
end
| FStar_Pervasives_Native.Some (head_type1) -> begin
(

let head_type2 = (

let uu____8393 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____8393))
in (

let uu____8394 = (curried_arrow_formals_comp head_type2)
in (match (uu____8394) with
| (formals, c) -> begin
(match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8410; FStar_Syntax_Syntax.vars = uu____8411}, uu____8412) when (Prims.op_Equality (FStar_List.length formals) (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (Prims.op_Equality (FStar_List.length formals) (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____8426 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (FStar_Pervasives_Native.Some (((formals), (c)))))
end
| uu____8439 -> begin
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

let uu____8475 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____8475) with
| (bs1, body1, opening) -> begin
(

let fallback = (fun uu____8498 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Imprecise function encoding"))))
in (

let uu____8505 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____8505), ((decl)::[]))))))
in (

let is_impure = (fun rc -> (

let uu____8512 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv rc.FStar_Syntax_Syntax.residual_effect)
in (FStar_All.pipe_right uu____8512 Prims.op_Negation)))
in (

let codomain_eff = (fun rc -> (

let res_typ = (match (rc.FStar_Syntax_Syntax.residual_typ) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8522 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____8522 FStar_Pervasives_Native.fst))
end
| FStar_Pervasives_Native.Some (t1) -> begin
t1
end)
in (match ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(

let uu____8542 = (FStar_Syntax_Syntax.mk_Total res_typ)
in FStar_Pervasives_Native.Some (uu____8542))
end
| uu____8543 -> begin
(match ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(

let uu____8546 = (FStar_Syntax_Syntax.mk_GTotal res_typ)
in FStar_Pervasives_Native.Some (uu____8546))
end
| uu____8547 -> begin
FStar_Pervasives_Native.None
end)
end)))
in (match (lopt) with
| FStar_Pervasives_Native.None -> begin
((

let uu____8553 = (

let uu____8554 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____8554))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____8553));
(fallback ());
)
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____8556 = ((is_impure rc) && (

let uu____8558 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (not (uu____8558))))
in (match (uu____8556) with
| true -> begin
(fallback ())
end
| uu____8563 -> begin
(

let cache_size = (FStar_Util.smap_size env.cache)
in (

let uu____8565 = (encode_binders FStar_Pervasives_Native.None bs1 env)
in (match (uu____8565) with
| (vars, guards, envbody, decls, uu____8590) -> begin
(

let body2 = (

let uu____8604 = (FStar_TypeChecker_Env.is_reifiable env.tcenv rc)
in (match (uu____8604) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.tcenv body1)
end
| uu____8605 -> begin
body1
end))
in (

let uu____8606 = (encode_term body2 envbody)
in (match (uu____8606) with
| (body3, decls') -> begin
(

let uu____8617 = (

let uu____8626 = (codomain_eff rc)
in (match (uu____8626) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), ([]))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs1 c)
in (

let uu____8645 = (encode_term tfun env)
in (match (uu____8645) with
| (t1, decls1) -> begin
((FStar_Pervasives_Native.Some (t1)), (decls1))
end)))
end))
in (match (uu____8617) with
| (arrow_t_opt, decls'') -> begin
(

let key_body = (

let uu____8677 = (

let uu____8688 = (

let uu____8689 = (

let uu____8694 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____8694), (body3)))
in (FStar_SMTEncoding_Util.mkImp uu____8689))
in (([]), (vars), (uu____8688)))
in (FStar_SMTEncoding_Util.mkForall uu____8677))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let cvars1 = (match (arrow_t_opt) with
| FStar_Pervasives_Native.None -> begin
cvars
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____8706 = (

let uu____8709 = (FStar_SMTEncoding_Term.free_variables t1)
in (FStar_List.append uu____8709 cvars))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____8706))
end)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars1), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____8728 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____8728) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____8736 = (

let uu____8737 = (

let uu____8744 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((cache_entry.cache_symbol_name), (uu____8744)))
in (FStar_SMTEncoding_Util.mkApp uu____8737))
in ((uu____8736), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8755 = (is_an_eta_expansion env vars body3)
in (match (uu____8755) with
| FStar_Pervasives_Native.Some (t1) -> begin
(

let decls1 = (

let uu____8766 = (

let uu____8767 = (FStar_Util.smap_size env.cache)
in (Prims.op_Equality uu____8767 cache_size))
in (match (uu____8766) with
| true -> begin
[]
end
| uu____8770 -> begin
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

let uu____8783 = (

let uu____8784 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____8784))
in (varops.mk_unique uu____8783))
in (Prims.strcat module_name (Prims.strcat "_" fsym))))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let f = (

let uu____8791 = (

let uu____8798 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((fsym), (uu____8798)))
in (FStar_SMTEncoding_Util.mkApp uu____8791))
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

let uu____8816 = (

let uu____8817 = (

let uu____8824 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars1), (f_has_t)))
in ((uu____8824), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____8817))
in (uu____8816)::[])))
end)
in (

let interp_f = (

let a_name = (Prims.strcat "interpretation_" fsym)
in (

let uu____8837 = (

let uu____8844 = (

let uu____8845 = (

let uu____8856 = (FStar_SMTEncoding_Util.mkEq ((app), (body3)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars1)), (uu____8856)))
in (FStar_SMTEncoding_Util.mkForall uu____8845))
in ((uu____8844), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____8837)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[])))))
in ((

let uu____8873 = (mk_cache_entry env fsym cvar_sorts f_decls)
in (FStar_Util.smap_add env.cache tkey_hash uu____8873));
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
| FStar_Syntax_Syntax.Tm_let ((uu____8876, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____8877); FStar_Syntax_Syntax.lbunivs = uu____8878; FStar_Syntax_Syntax.lbtyp = uu____8879; FStar_Syntax_Syntax.lbeff = uu____8880; FStar_Syntax_Syntax.lbdef = uu____8881})::uu____8882), uu____8883) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____8909; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____8911; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____8932) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(FStar_Exn.raise Inner_let_rec);
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____9002 = (encode_term e1 env)
in (match (uu____9002) with
| (ee1, decls1) -> begin
(

let uu____9013 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) e2)
in (match (uu____9013) with
| (xs, e21) -> begin
(

let uu____9038 = (FStar_List.hd xs)
in (match (uu____9038) with
| (x1, uu____9052) -> begin
(

let env' = (push_term_var env x1 ee1)
in (

let uu____9054 = (encode_body e21 env')
in (match (uu____9054) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____9086 = (

let uu____9093 = (

let uu____9094 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_bv uu____9094))
in (gen_term_var env uu____9093))
in (match (uu____9086) with
| (scrsym, scr', env1) -> begin
(

let uu____9102 = (encode_term e env1)
in (match (uu____9102) with
| (scr, decls) -> begin
(

let uu____9113 = (

let encode_branch = (fun b uu____9138 -> (match (uu____9138) with
| (else_case, decls1) -> begin
(

let uu____9157 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____9157) with
| (p, w, br) -> begin
(

let uu____9183 = (encode_pat env1 p)
in (match (uu____9183) with
| (env0, pattern) -> begin
(

let guard = (pattern.guard scr')
in (

let projections = (pattern.projections scr')
in (

let env2 = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env2 uu____9220 -> (match (uu____9220) with
| (x, t) -> begin
(push_term_var env2 x t)
end)) env1))
in (

let uu____9227 = (match (w) with
| FStar_Pervasives_Native.None -> begin
((guard), ([]))
end
| FStar_Pervasives_Native.Some (w1) -> begin
(

let uu____9249 = (encode_term w1 env2)
in (match (uu____9249) with
| (w2, decls2) -> begin
(

let uu____9262 = (

let uu____9263 = (

let uu____9268 = (

let uu____9269 = (

let uu____9274 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w2), (uu____9274)))
in (FStar_SMTEncoding_Util.mkEq uu____9269))
in ((guard), (uu____9268)))
in (FStar_SMTEncoding_Util.mkAnd uu____9263))
in ((uu____9262), (decls2)))
end))
end)
in (match (uu____9227) with
| (guard1, decls2) -> begin
(

let uu____9287 = (encode_br br env2)
in (match (uu____9287) with
| (br1, decls3) -> begin
(

let uu____9300 = (FStar_SMTEncoding_Util.mkITE ((guard1), (br1), (else_case)))
in ((uu____9300), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end)))))
end))
end))
end))
in (FStar_List.fold_right encode_branch pats ((default_case), (decls))))
in (match (uu____9113) with
| (match_tm, decls1) -> begin
(

let uu____9319 = (FStar_SMTEncoding_Term.mkLet' (((((((scrsym), (FStar_SMTEncoding_Term.Term_sort))), (scr)))::[]), (match_tm)) FStar_Range.dummyRange)
in ((uu____9319), (decls1)))
end))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____9359 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____9359) with
| true -> begin
(

let uu____9360 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____9360))
end
| uu____9361 -> begin
()
end));
(

let uu____9362 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____9362) with
| (vars, pat_term) -> begin
(

let uu____9379 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____9432 v1 -> (match (uu____9432) with
| (env1, vars1) -> begin
(

let uu____9484 = (gen_term_var env1 v1)
in (match (uu____9484) with
| (xx, uu____9506, env2) -> begin
((env2), ((((v1), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars1))
end))
end)) ((env), ([]))))
in (match (uu____9379) with
| (env1, vars1) -> begin
(

let rec mk_guard = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (uu____9585) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_wild (uu____9586) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____9587) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____9595 = (

let uu____9600 = (encode_const c)
in ((scrutinee), (uu____9600)))
in (FStar_SMTEncoding_Util.mkEq uu____9595))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (

let tc_name = (FStar_TypeChecker_Env.typ_of_datacon env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____9621 = (FStar_TypeChecker_Env.datacons_of_typ env1.tcenv tc_name)
in (match (uu____9621) with
| (uu____9628, (uu____9629)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____9632 -> begin
(mk_data_tester env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
end)))
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____9665 -> (match (uu____9665) with
| (arg, uu____9673) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____9679 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____9679)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____9706) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____9737) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____9760 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____9804 -> (match (uu____9804) with
| (arg, uu____9818) -> begin
(

let proj = (primitive_projector_by_pos env1.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____9824 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____9824)))
end))))
in (FStar_All.pipe_right uu____9760 FStar_List.flatten))
end))
in (

let pat_term1 = (fun uu____9852 -> (encode_term pat_term env1))
in (

let pattern = {pat_vars = vars1; pat_term = pat_term1; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env1), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____9862 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____9900 uu____9901 -> (match (((uu____9900), (uu____9901))) with
| ((tms, decls), (t, uu____9937)) -> begin
(

let uu____9958 = (encode_term t env)
in (match (uu____9958) with
| (t1, decls') -> begin
(((t1)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____9862) with
| (l1, decls) -> begin
(((FStar_List.rev l1)), (decls))
end)))
and encode_function_type_as_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let list_elements1 = (fun e -> (

let uu____10015 = (FStar_Syntax_Util.list_elements e)
in (match (uu____10015) with
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

let uu____10036 = (

let uu____10051 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____10051 FStar_Syntax_Util.head_and_args))
in (match (uu____10036) with
| (head1, args) -> begin
(

let uu____10090 = (

let uu____10103 = (

let uu____10104 = (FStar_Syntax_Util.un_uinst head1)
in uu____10104.FStar_Syntax_Syntax.n)
in ((uu____10103), (args)))
in (match (uu____10090) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____10118, uu____10119))::((e, uu____10121))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
e
end
| uu____10156 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements1 p)
in (

let smt_pat_or1 = (fun t1 -> (

let uu____10192 = (

let uu____10207 = (FStar_Syntax_Util.unmeta t1)
in (FStar_All.pipe_right uu____10207 FStar_Syntax_Util.head_and_args))
in (match (uu____10192) with
| (head1, args) -> begin
(

let uu____10248 = (

let uu____10261 = (

let uu____10262 = (FStar_Syntax_Util.un_uinst head1)
in uu____10262.FStar_Syntax_Syntax.n)
in ((uu____10261), (args)))
in (match (uu____10248) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____10279))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
FStar_Pervasives_Native.Some (e)
end
| uu____10306 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (elts) with
| (t1)::[] -> begin
(

let uu____10328 = (smt_pat_or1 t1)
in (match (uu____10328) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____10344 = (list_elements1 e)
in (FStar_All.pipe_right uu____10344 (FStar_List.map (fun branch1 -> (

let uu____10362 = (list_elements1 branch1)
in (FStar_All.pipe_right uu____10362 (FStar_List.map one_pat)))))))
end
| uu____10373 -> begin
(

let uu____10378 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____10378)::[])
end))
end
| uu____10399 -> begin
(

let uu____10402 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____10402)::[])
end))))
in (

let uu____10423 = (

let uu____10442 = (

let uu____10443 = (FStar_Syntax_Subst.compress t)
in uu____10443.FStar_Syntax_Syntax.n)
in (match (uu____10442) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____10482 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____10482) with
| (binders1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____10525; FStar_Syntax_Syntax.effect_name = uu____10526; FStar_Syntax_Syntax.result_typ = uu____10527; FStar_Syntax_Syntax.effect_args = ((pre, uu____10529))::((post, uu____10531))::((pats, uu____10533))::[]; FStar_Syntax_Syntax.flags = uu____10534}) -> begin
(

let uu____10575 = (lemma_pats pats)
in ((binders1), (pre), (post), (uu____10575)))
end
| uu____10592 -> begin
(failwith "impos")
end)
end))
end
| uu____10611 -> begin
(failwith "Impos")
end))
in (match (uu____10423) with
| (binders, pre, post, patterns) -> begin
(

let env1 = (

let uu___142_10659 = env
in {bindings = uu___142_10659.bindings; depth = uu___142_10659.depth; tcenv = uu___142_10659.tcenv; warn = uu___142_10659.warn; cache = uu___142_10659.cache; nolabels = uu___142_10659.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___142_10659.encode_non_total_function_typ; current_module_name = uu___142_10659.current_module_name})
in (

let uu____10660 = (encode_binders FStar_Pervasives_Native.None binders env1)
in (match (uu____10660) with
| (vars, guards, env2, decls, uu____10685) -> begin
(

let uu____10698 = (

let uu____10711 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch1 -> (

let uu____10755 = (

let uu____10764 = (FStar_All.pipe_right branch1 (FStar_List.map (fun t1 -> (encode_term t1 env2))))
in (FStar_All.pipe_right uu____10764 FStar_List.unzip))
in (match (uu____10755) with
| (pats, decls1) -> begin
((pats), (decls1))
end)))))
in (FStar_All.pipe_right uu____10711 FStar_List.unzip))
in (match (uu____10698) with
| (pats, decls') -> begin
(

let decls'1 = (FStar_List.flatten decls')
in (

let env3 = (

let uu___143_10873 = env2
in {bindings = uu___143_10873.bindings; depth = uu___143_10873.depth; tcenv = uu___143_10873.tcenv; warn = uu___143_10873.warn; cache = uu___143_10873.cache; nolabels = true; use_zfuel_name = uu___143_10873.use_zfuel_name; encode_non_total_function_typ = uu___143_10873.encode_non_total_function_typ; current_module_name = uu___143_10873.current_module_name})
in (

let uu____10874 = (

let uu____10879 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____10879 env3))
in (match (uu____10874) with
| (pre1, decls'') -> begin
(

let uu____10886 = (

let uu____10891 = (FStar_Syntax_Util.unmeta post)
in (encode_formula uu____10891 env3))
in (match (uu____10886) with
| (post1, decls''') -> begin
(

let decls1 = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls'1) (FStar_List.append decls'' decls''')))
in (

let uu____10901 = (

let uu____10902 = (

let uu____10913 = (

let uu____10914 = (

let uu____10919 = (FStar_SMTEncoding_Util.mk_and_l ((pre1)::guards))
in ((uu____10919), (post1)))
in (FStar_SMTEncoding_Util.mkImp uu____10914))
in ((pats), (vars), (uu____10913)))
in (FStar_SMTEncoding_Util.mkForall uu____10902))
in ((uu____10901), (decls1))))
end))
end))))
end))
end)))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug1 = (fun phi1 -> (

let uu____10938 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____10938) with
| true -> begin
(

let uu____10939 = (FStar_Syntax_Print.tag_of_term phi1)
in (

let uu____10940 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____10939 uu____10940)))
end
| uu____10941 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____10973 = (FStar_Util.fold_map (fun decls x -> (

let uu____11001 = (encode_term (FStar_Pervasives_Native.fst x) env)
in (match (uu____11001) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____10973) with
| (decls, args) -> begin
(

let uu____11030 = (

let uu___144_11031 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___144_11031.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___144_11031.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____11030), (decls)))
end)))
in (

let const_op = (fun f r uu____11062 -> (

let uu____11075 = (f r)
in ((uu____11075), ([]))))
in (

let un_op = (fun f l -> (

let uu____11094 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____11094)))
in (

let bin_op = (fun f uu___118_11110 -> (match (uu___118_11110) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____11121 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____11155 = (FStar_Util.fold_map (fun decls uu____11178 -> (match (uu____11178) with
| (t, uu____11192) -> begin
(

let uu____11193 = (encode_formula t env)
in (match (uu____11193) with
| (phi1, decls') -> begin
(((FStar_List.append decls decls')), (phi1))
end))
end)) [] l)
in (match (uu____11155) with
| (decls, phis) -> begin
(

let uu____11222 = (

let uu___145_11223 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___145_11223.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___145_11223.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____11222), (decls)))
end)))
in (

let eq_op = (fun r args -> (

let rf = (FStar_List.filter (fun uu____11284 -> (match (uu____11284) with
| (a, q) -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____11303)) -> begin
false
end
| uu____11304 -> begin
true
end)
end)) args)
in (match ((Prims.op_disEquality (FStar_List.length rf) (Prims.parse_int "2"))) with
| true -> begin
(

let uu____11319 = (FStar_Util.format1 "eq_op: got %s non-implicit arguments instead of 2?" (Prims.string_of_int (FStar_List.length rf)))
in (failwith uu____11319))
end
| uu____11332 -> begin
(

let uu____11333 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____11333 r rf))
end)))
in (

let mk_imp1 = (fun r uu___119_11358 -> (match (uu___119_11358) with
| ((lhs, uu____11364))::((rhs, uu____11366))::[] -> begin
(

let uu____11393 = (encode_formula rhs env)
in (match (uu____11393) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____11408) -> begin
((l1), (decls1))
end
| uu____11413 -> begin
(

let uu____11414 = (encode_formula lhs env)
in (match (uu____11414) with
| (l2, decls2) -> begin
(

let uu____11425 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____11425), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____11428 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___120_11449 -> (match (uu___120_11449) with
| ((guard, uu____11455))::((_then, uu____11457))::((_else, uu____11459))::[] -> begin
(

let uu____11496 = (encode_formula guard env)
in (match (uu____11496) with
| (g, decls1) -> begin
(

let uu____11507 = (encode_formula _then env)
in (match (uu____11507) with
| (t, decls2) -> begin
(

let uu____11518 = (encode_formula _else env)
in (match (uu____11518) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____11532 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____11557 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____11557)))
in (

let connectives = (

let uu____11575 = (

let uu____11588 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Parser_Const.and_lid), (uu____11588)))
in (

let uu____11605 = (

let uu____11620 = (

let uu____11633 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Parser_Const.or_lid), (uu____11633)))
in (

let uu____11650 = (

let uu____11665 = (

let uu____11680 = (

let uu____11693 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Parser_Const.iff_lid), (uu____11693)))
in (

let uu____11710 = (

let uu____11725 = (

let uu____11740 = (

let uu____11753 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Parser_Const.not_lid), (uu____11753)))
in (uu____11740)::(((FStar_Parser_Const.eq2_lid), (eq_op)))::(((FStar_Parser_Const.eq3_lid), (eq_op)))::(((FStar_Parser_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Parser_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Parser_Const.ite_lid), (mk_ite)))::uu____11725)
in (uu____11680)::uu____11710))
in (((FStar_Parser_Const.imp_lid), (mk_imp1)))::uu____11665)
in (uu____11620)::uu____11650))
in (uu____11575)::uu____11605))
in (

let rec fallback = (fun phi1 -> (match (phi1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____12074 = (encode_formula phi' env)
in (match (uu____12074) with
| (phi2, decls) -> begin
(

let uu____12085 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi2), (msg), (r)))) r)
in ((uu____12085), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____12086) -> begin
(

let uu____12093 = (FStar_Syntax_Util.unmeta phi1)
in (encode_formula uu____12093 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____12132 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____12132) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____12144; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____12146; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____12167 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____12167) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____12214)::((x, uu____12216))::((t, uu____12218))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid) -> begin
(

let uu____12265 = (encode_term x env)
in (match (uu____12265) with
| (x1, decls) -> begin
(

let uu____12276 = (encode_term t env)
in (match (uu____12276) with
| (t1, decls') -> begin
(

let uu____12287 = (FStar_SMTEncoding_Term.mk_HasType x1 t1)
in ((uu____12287), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____12292))::((msg, uu____12294))::((phi2, uu____12296))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.labeled_lid) -> begin
(

let uu____12341 = (

let uu____12346 = (

let uu____12347 = (FStar_Syntax_Subst.compress r)
in uu____12347.FStar_Syntax_Syntax.n)
in (

let uu____12350 = (

let uu____12351 = (FStar_Syntax_Subst.compress msg)
in uu____12351.FStar_Syntax_Syntax.n)
in ((uu____12346), (uu____12350))))
in (match (uu____12341) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____12360))) -> begin
(

let phi3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi2), (FStar_Syntax_Syntax.Meta_labeled (((s), (r1), (false))))))) FStar_Pervasives_Native.None r1)
in (fallback phi3))
end
| uu____12366 -> begin
(fallback phi2)
end))
end
| uu____12371 when (head_redex env head2) -> begin
(

let uu____12384 = (whnf env phi1)
in (encode_formula uu____12384 env))
end
| uu____12385 -> begin
(

let uu____12398 = (encode_term phi1 env)
in (match (uu____12398) with
| (tt, decls) -> begin
(

let uu____12409 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___146_12412 = tt
in {FStar_SMTEncoding_Term.tm = uu___146_12412.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___146_12412.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____12409), (decls)))
end))
end))
end
| uu____12413 -> begin
(

let uu____12414 = (encode_term phi1 env)
in (match (uu____12414) with
| (tt, decls) -> begin
(

let uu____12425 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___147_12428 = tt
in {FStar_SMTEncoding_Term.tm = uu___147_12428.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___147_12428.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____12425), (decls)))
end))
end))
in (

let encode_q_body = (fun env1 bs ps body -> (

let uu____12464 = (encode_binders FStar_Pervasives_Native.None bs env1)
in (match (uu____12464) with
| (vars, guards, env2, decls, uu____12503) -> begin
(

let uu____12516 = (

let uu____12529 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____12577 = (

let uu____12586 = (FStar_All.pipe_right p (FStar_List.map (fun uu____12616 -> (match (uu____12616) with
| (t, uu____12626) -> begin
(encode_term t (

let uu___148_12628 = env2
in {bindings = uu___148_12628.bindings; depth = uu___148_12628.depth; tcenv = uu___148_12628.tcenv; warn = uu___148_12628.warn; cache = uu___148_12628.cache; nolabels = uu___148_12628.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___148_12628.encode_non_total_function_typ; current_module_name = uu___148_12628.current_module_name}))
end))))
in (FStar_All.pipe_right uu____12586 FStar_List.unzip))
in (match (uu____12577) with
| (p1, decls1) -> begin
((p1), ((FStar_List.flatten decls1)))
end)))))
in (FStar_All.pipe_right uu____12529 FStar_List.unzip))
in (match (uu____12516) with
| (pats, decls') -> begin
(

let uu____12727 = (encode_formula body env2)
in (match (uu____12727) with
| (body1, decls'') -> begin
(

let guards1 = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____12759; FStar_SMTEncoding_Term.rng = uu____12760})::[])::[] when (Prims.op_Equality (FStar_Ident.text_of_lid FStar_Parser_Const.guard_free) gf) -> begin
[]
end
| uu____12775 -> begin
guards
end)
in (

let uu____12780 = (FStar_SMTEncoding_Util.mk_and_l guards1)
in ((vars), (pats), (uu____12780), (body1), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug1 phi);
(

let phi1 = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____12840 -> (match (uu____12840) with
| (x, uu____12846) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats1) with
| [] -> begin
()
end
| (hd1)::tl1 -> begin
(

let pat_vars = (

let uu____12854 = (FStar_Syntax_Free.names hd1)
in (FStar_List.fold_left (fun out x -> (

let uu____12866 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____12866))) uu____12854 tl1))
in (

let uu____12869 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____12896 -> (match (uu____12896) with
| (b, uu____12902) -> begin
(

let uu____12903 = (FStar_Util.set_mem b pat_vars)
in (not (uu____12903)))
end))))
in (match (uu____12869) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____12909) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd1.FStar_Syntax_Syntax.pos tl1)
in (

let uu____12923 = (

let uu____12924 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____12924))
in (FStar_Errors.warn pos uu____12923)))
end)))
end)))
in (

let uu____12925 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____12925) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____12934 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____12992 -> (match (uu____12992) with
| (l, uu____13006) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____12934) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (uu____13039, f) -> begin
(f phi1.FStar_Syntax_Syntax.pos arms)
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____13079 = (encode_q_body env vars pats body)
in (match (uu____13079) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let tm = (

let uu____13124 = (

let uu____13135 = (FStar_SMTEncoding_Util.mkImp ((guard), (body1)))
in ((pats1), (vars1), (uu____13135)))
in (FStar_SMTEncoding_Term.mkForall uu____13124 phi1.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____13154 = (encode_q_body env vars pats body)
in (match (uu____13154) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let uu____13198 = (

let uu____13199 = (

let uu____13210 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body1)))
in ((pats1), (vars1), (uu____13210)))
in (FStar_SMTEncoding_Term.mkExists uu____13199 phi1.FStar_Syntax_Syntax.pos))
in ((uu____13198), (decls)))
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

let uu____13308 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13308) with
| (asym, a) -> begin
(

let uu____13315 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13315) with
| (xsym, x) -> begin
(

let uu____13322 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13322) with
| (ysym, y) -> begin
(

let quant = (fun vars body x1 -> (

let xname_decl = (

let uu____13366 = (

let uu____13377 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in ((x1), (uu____13377), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____13366))
in (

let xtok = (Prims.strcat x1 "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let xapp = (

let uu____13403 = (

let uu____13410 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x1), (uu____13410)))
in (FStar_SMTEncoding_Util.mkApp uu____13403))
in (

let xtok1 = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok1 vars)
in (

let uu____13423 = (

let uu____13426 = (

let uu____13429 = (

let uu____13432 = (

let uu____13433 = (

let uu____13440 = (

let uu____13441 = (

let uu____13452 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____13452)))
in (FStar_SMTEncoding_Util.mkForall uu____13441))
in ((uu____13440), (FStar_Pervasives_Native.None), ((Prims.strcat "primitive_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____13433))
in (

let uu____13469 = (

let uu____13472 = (

let uu____13473 = (

let uu____13480 = (

let uu____13481 = (

let uu____13492 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____13492)))
in (FStar_SMTEncoding_Util.mkForall uu____13481))
in ((uu____13480), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" x1))))
in (FStar_SMTEncoding_Util.mkAssume uu____13473))
in (uu____13472)::[])
in (uu____13432)::uu____13469))
in (xtok_decl)::uu____13429)
in (xname_decl)::uu____13426)
in ((xtok1), (uu____13423))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims1 = (

let uu____13583 = (

let uu____13596 = (

let uu____13605 = (

let uu____13606 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13606))
in (quant axy uu____13605))
in ((FStar_Parser_Const.op_Eq), (uu____13596)))
in (

let uu____13615 = (

let uu____13630 = (

let uu____13643 = (

let uu____13652 = (

let uu____13653 = (

let uu____13654 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____13654))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13653))
in (quant axy uu____13652))
in ((FStar_Parser_Const.op_notEq), (uu____13643)))
in (

let uu____13663 = (

let uu____13678 = (

let uu____13691 = (

let uu____13700 = (

let uu____13701 = (

let uu____13702 = (

let uu____13707 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13708 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13707), (uu____13708))))
in (FStar_SMTEncoding_Util.mkLT uu____13702))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13701))
in (quant xy uu____13700))
in ((FStar_Parser_Const.op_LT), (uu____13691)))
in (

let uu____13717 = (

let uu____13732 = (

let uu____13745 = (

let uu____13754 = (

let uu____13755 = (

let uu____13756 = (

let uu____13761 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13762 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13761), (uu____13762))))
in (FStar_SMTEncoding_Util.mkLTE uu____13756))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13755))
in (quant xy uu____13754))
in ((FStar_Parser_Const.op_LTE), (uu____13745)))
in (

let uu____13771 = (

let uu____13786 = (

let uu____13799 = (

let uu____13808 = (

let uu____13809 = (

let uu____13810 = (

let uu____13815 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13816 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13815), (uu____13816))))
in (FStar_SMTEncoding_Util.mkGT uu____13810))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13809))
in (quant xy uu____13808))
in ((FStar_Parser_Const.op_GT), (uu____13799)))
in (

let uu____13825 = (

let uu____13840 = (

let uu____13853 = (

let uu____13862 = (

let uu____13863 = (

let uu____13864 = (

let uu____13869 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13870 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13869), (uu____13870))))
in (FStar_SMTEncoding_Util.mkGTE uu____13864))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____13863))
in (quant xy uu____13862))
in ((FStar_Parser_Const.op_GTE), (uu____13853)))
in (

let uu____13879 = (

let uu____13894 = (

let uu____13907 = (

let uu____13916 = (

let uu____13917 = (

let uu____13918 = (

let uu____13923 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____13924 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____13923), (uu____13924))))
in (FStar_SMTEncoding_Util.mkSub uu____13918))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13917))
in (quant xy uu____13916))
in ((FStar_Parser_Const.op_Subtraction), (uu____13907)))
in (

let uu____13933 = (

let uu____13948 = (

let uu____13961 = (

let uu____13970 = (

let uu____13971 = (

let uu____13972 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____13972))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____13971))
in (quant qx uu____13970))
in ((FStar_Parser_Const.op_Minus), (uu____13961)))
in (

let uu____13981 = (

let uu____13996 = (

let uu____14009 = (

let uu____14018 = (

let uu____14019 = (

let uu____14020 = (

let uu____14025 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14026 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14025), (uu____14026))))
in (FStar_SMTEncoding_Util.mkAdd uu____14020))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14019))
in (quant xy uu____14018))
in ((FStar_Parser_Const.op_Addition), (uu____14009)))
in (

let uu____14035 = (

let uu____14050 = (

let uu____14063 = (

let uu____14072 = (

let uu____14073 = (

let uu____14074 = (

let uu____14079 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14080 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14079), (uu____14080))))
in (FStar_SMTEncoding_Util.mkMul uu____14074))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14073))
in (quant xy uu____14072))
in ((FStar_Parser_Const.op_Multiply), (uu____14063)))
in (

let uu____14089 = (

let uu____14104 = (

let uu____14117 = (

let uu____14126 = (

let uu____14127 = (

let uu____14128 = (

let uu____14133 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14134 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14133), (uu____14134))))
in (FStar_SMTEncoding_Util.mkDiv uu____14128))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14127))
in (quant xy uu____14126))
in ((FStar_Parser_Const.op_Division), (uu____14117)))
in (

let uu____14143 = (

let uu____14158 = (

let uu____14171 = (

let uu____14180 = (

let uu____14181 = (

let uu____14182 = (

let uu____14187 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____14188 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____14187), (uu____14188))))
in (FStar_SMTEncoding_Util.mkMod uu____14182))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____14181))
in (quant xy uu____14180))
in ((FStar_Parser_Const.op_Modulus), (uu____14171)))
in (

let uu____14197 = (

let uu____14212 = (

let uu____14225 = (

let uu____14234 = (

let uu____14235 = (

let uu____14236 = (

let uu____14241 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____14242 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____14241), (uu____14242))))
in (FStar_SMTEncoding_Util.mkAnd uu____14236))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14235))
in (quant xy uu____14234))
in ((FStar_Parser_Const.op_And), (uu____14225)))
in (

let uu____14251 = (

let uu____14266 = (

let uu____14279 = (

let uu____14288 = (

let uu____14289 = (

let uu____14290 = (

let uu____14295 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____14296 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____14295), (uu____14296))))
in (FStar_SMTEncoding_Util.mkOr uu____14290))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14289))
in (quant xy uu____14288))
in ((FStar_Parser_Const.op_Or), (uu____14279)))
in (

let uu____14305 = (

let uu____14320 = (

let uu____14333 = (

let uu____14342 = (

let uu____14343 = (

let uu____14344 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____14344))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____14343))
in (quant qx uu____14342))
in ((FStar_Parser_Const.op_Negation), (uu____14333)))
in (uu____14320)::[])
in (uu____14266)::uu____14305))
in (uu____14212)::uu____14251))
in (uu____14158)::uu____14197))
in (uu____14104)::uu____14143))
in (uu____14050)::uu____14089))
in (uu____13996)::uu____14035))
in (uu____13948)::uu____13981))
in (uu____13894)::uu____13933))
in (uu____13840)::uu____13879))
in (uu____13786)::uu____13825))
in (uu____13732)::uu____13771))
in (uu____13678)::uu____13717))
in (uu____13630)::uu____13663))
in (uu____13583)::uu____13615))
in (

let mk1 = (fun l v1 -> (

let uu____14558 = (

let uu____14567 = (FStar_All.pipe_right prims1 (FStar_List.find (fun uu____14625 -> (match (uu____14625) with
| (l', uu____14639) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____14567 (FStar_Option.map (fun uu____14699 -> (match (uu____14699) with
| (uu____14718, b) -> begin
(b v1)
end)))))
in (FStar_All.pipe_right uu____14558 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims1 (FStar_Util.for_some (fun uu____14789 -> (match (uu____14789) with
| (l', uu____14803) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk1; is = is})))))))
end))
end))
end))


let pretype_axiom : env_t  ->  FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun env tapp vars -> (

let uu____14844 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____14844) with
| (xxsym, xx) -> begin
(

let uu____14851 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____14851) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let module_name = env.current_module_name
in (

let uu____14861 = (

let uu____14868 = (

let uu____14869 = (

let uu____14880 = (

let uu____14881 = (

let uu____14886 = (

let uu____14887 = (

let uu____14892 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____14892)))
in (FStar_SMTEncoding_Util.mkEq uu____14887))
in ((xx_has_type), (uu____14886)))
in (FStar_SMTEncoding_Util.mkImp uu____14881))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____14880)))
in (FStar_SMTEncoding_Util.mkForall uu____14869))
in (

let uu____14917 = (

let uu____14918 = (

let uu____14919 = (

let uu____14920 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "_pretyping_" uu____14920))
in (Prims.strcat module_name uu____14919))
in (varops.mk_unique uu____14918))
in ((uu____14868), (FStar_Pervasives_Native.Some ("pretyping")), (uu____14917))))
in (FStar_SMTEncoding_Util.mkAssume uu____14861)))))
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

let uu____14960 = (

let uu____14961 = (

let uu____14968 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____14968), (FStar_Pervasives_Native.Some ("unit typing")), ("unit_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____14961))
in (

let uu____14971 = (

let uu____14974 = (

let uu____14975 = (

let uu____14982 = (

let uu____14983 = (

let uu____14994 = (

let uu____14995 = (

let uu____15000 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____15000)))
in (FStar_SMTEncoding_Util.mkImp uu____14995))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____14994)))
in (mkForall_fuel uu____14983))
in ((uu____14982), (FStar_Pervasives_Native.Some ("unit inversion")), ("unit_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____14975))
in (uu____14974)::[])
in (uu____14960)::uu____14971))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____15042 = (

let uu____15043 = (

let uu____15050 = (

let uu____15051 = (

let uu____15062 = (

let uu____15067 = (

let uu____15070 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____15070)::[])
in (uu____15067)::[])
in (

let uu____15075 = (

let uu____15076 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____15076 tt))
in ((uu____15062), ((bb)::[]), (uu____15075))))
in (FStar_SMTEncoding_Util.mkForall uu____15051))
in ((uu____15050), (FStar_Pervasives_Native.Some ("bool typing")), ("bool_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15043))
in (

let uu____15097 = (

let uu____15100 = (

let uu____15101 = (

let uu____15108 = (

let uu____15109 = (

let uu____15120 = (

let uu____15121 = (

let uu____15126 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxBoolFun) x)
in ((typing_pred), (uu____15126)))
in (FStar_SMTEncoding_Util.mkImp uu____15121))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15120)))
in (mkForall_fuel uu____15109))
in ((uu____15108), (FStar_Pervasives_Native.Some ("bool inversion")), ("bool_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15101))
in (uu____15100)::[])
in (uu____15042)::uu____15097))))))
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

let uu____15176 = (

let uu____15177 = (

let uu____15184 = (

let uu____15187 = (

let uu____15190 = (

let uu____15193 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____15194 = (

let uu____15197 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____15197)::[])
in (uu____15193)::uu____15194))
in (tt)::uu____15190)
in (tt)::uu____15187)
in (("Prims.Precedes"), (uu____15184)))
in (FStar_SMTEncoding_Util.mkApp uu____15177))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15176))
in (

let precedes_y_x = (

let uu____15201 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15201))
in (

let uu____15204 = (

let uu____15205 = (

let uu____15212 = (

let uu____15213 = (

let uu____15224 = (

let uu____15229 = (

let uu____15232 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____15232)::[])
in (uu____15229)::[])
in (

let uu____15237 = (

let uu____15238 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____15238 tt))
in ((uu____15224), ((bb)::[]), (uu____15237))))
in (FStar_SMTEncoding_Util.mkForall uu____15213))
in ((uu____15212), (FStar_Pervasives_Native.Some ("int typing")), ("int_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15205))
in (

let uu____15259 = (

let uu____15262 = (

let uu____15263 = (

let uu____15270 = (

let uu____15271 = (

let uu____15282 = (

let uu____15283 = (

let uu____15288 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxIntFun) x)
in ((typing_pred), (uu____15288)))
in (FStar_SMTEncoding_Util.mkImp uu____15283))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15282)))
in (mkForall_fuel uu____15271))
in ((uu____15270), (FStar_Pervasives_Native.Some ("int inversion")), ("int_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15263))
in (

let uu____15313 = (

let uu____15316 = (

let uu____15317 = (

let uu____15324 = (

let uu____15325 = (

let uu____15336 = (

let uu____15337 = (

let uu____15342 = (

let uu____15343 = (

let uu____15346 = (

let uu____15349 = (

let uu____15352 = (

let uu____15353 = (

let uu____15358 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____15359 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____15358), (uu____15359))))
in (FStar_SMTEncoding_Util.mkGT uu____15353))
in (

let uu____15360 = (

let uu____15363 = (

let uu____15364 = (

let uu____15369 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____15370 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____15369), (uu____15370))))
in (FStar_SMTEncoding_Util.mkGTE uu____15364))
in (

let uu____15371 = (

let uu____15374 = (

let uu____15375 = (

let uu____15380 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____15381 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____15380), (uu____15381))))
in (FStar_SMTEncoding_Util.mkLT uu____15375))
in (uu____15374)::[])
in (uu____15363)::uu____15371))
in (uu____15352)::uu____15360))
in (typing_pred_y)::uu____15349)
in (typing_pred)::uu____15346)
in (FStar_SMTEncoding_Util.mk_and_l uu____15343))
in ((uu____15342), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____15337))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____15336)))
in (mkForall_fuel uu____15325))
in ((uu____15324), (FStar_Pervasives_Native.Some ("well-founded ordering on nat (alt)")), ("well-founded-ordering-on-nat")))
in (FStar_SMTEncoding_Util.mkAssume uu____15317))
in (uu____15316)::[])
in (uu____15262)::uu____15313))
in (uu____15204)::uu____15259)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____15427 = (

let uu____15428 = (

let uu____15435 = (

let uu____15436 = (

let uu____15447 = (

let uu____15452 = (

let uu____15455 = (FStar_SMTEncoding_Term.boxString b)
in (uu____15455)::[])
in (uu____15452)::[])
in (

let uu____15460 = (

let uu____15461 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____15461 tt))
in ((uu____15447), ((bb)::[]), (uu____15460))))
in (FStar_SMTEncoding_Util.mkForall uu____15436))
in ((uu____15435), (FStar_Pervasives_Native.Some ("string typing")), ("string_typing")))
in (FStar_SMTEncoding_Util.mkAssume uu____15428))
in (

let uu____15482 = (

let uu____15485 = (

let uu____15486 = (

let uu____15493 = (

let uu____15494 = (

let uu____15505 = (

let uu____15506 = (

let uu____15511 = (FStar_SMTEncoding_Term.mk_tester (FStar_Pervasives_Native.fst FStar_SMTEncoding_Term.boxStringFun) x)
in ((typing_pred), (uu____15511)))
in (FStar_SMTEncoding_Util.mkImp uu____15506))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____15505)))
in (mkForall_fuel uu____15494))
in ((uu____15493), (FStar_Pervasives_Native.Some ("string inversion")), ("string_inversion")))
in (FStar_SMTEncoding_Util.mkAssume uu____15486))
in (uu____15485)::[])
in (uu____15427)::uu____15482))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in ((FStar_SMTEncoding_Util.mkAssume ((valid), (FStar_Pervasives_Native.Some ("True interpretation")), ("true_interp"))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____15564 = (

let uu____15565 = (

let uu____15572 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____15572), (FStar_Pervasives_Native.Some ("False interpretation")), ("false_interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15565))
in (uu____15564)::[])))
in (

let mk_and_interp = (fun env conj uu____15584 -> (

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

let uu____15609 = (

let uu____15610 = (

let uu____15617 = (

let uu____15618 = (

let uu____15629 = (

let uu____15630 = (

let uu____15635 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____15635), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15630))
in ((((l_and_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15629)))
in (FStar_SMTEncoding_Util.mkForall uu____15618))
in ((uu____15617), (FStar_Pervasives_Native.Some ("/\\ interpretation")), ("l_and-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15610))
in (uu____15609)::[]))))))))))
in (

let mk_or_interp = (fun env disj uu____15673 -> (

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

let uu____15698 = (

let uu____15699 = (

let uu____15706 = (

let uu____15707 = (

let uu____15718 = (

let uu____15719 = (

let uu____15724 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____15724), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15719))
in ((((l_or_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____15718)))
in (FStar_SMTEncoding_Util.mkForall uu____15707))
in ((uu____15706), (FStar_Pervasives_Native.Some ("\\/ interpretation")), ("l_or-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15699))
in (uu____15698)::[]))))))))))
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

let uu____15787 = (

let uu____15788 = (

let uu____15795 = (

let uu____15796 = (

let uu____15807 = (

let uu____15808 = (

let uu____15813 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____15813), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15808))
in ((((eq2_x_y)::[])::[]), ((aa)::(xx1)::(yy1)::[]), (uu____15807)))
in (FStar_SMTEncoding_Util.mkForall uu____15796))
in ((uu____15795), (FStar_Pervasives_Native.Some ("Eq2 interpretation")), ("eq2-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15788))
in (uu____15787)::[]))))))))))
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

let uu____15886 = (

let uu____15887 = (

let uu____15894 = (

let uu____15895 = (

let uu____15906 = (

let uu____15907 = (

let uu____15912 = (FStar_SMTEncoding_Util.mkEq ((x1), (y1)))
in ((uu____15912), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____15907))
in ((((eq3_x_y)::[])::[]), ((aa)::(bb)::(xx1)::(yy1)::[]), (uu____15906)))
in (FStar_SMTEncoding_Util.mkForall uu____15895))
in ((uu____15894), (FStar_Pervasives_Native.Some ("Eq3 interpretation")), ("eq3-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15887))
in (uu____15886)::[]))))))))))))
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

let uu____15983 = (

let uu____15984 = (

let uu____15991 = (

let uu____15992 = (

let uu____16003 = (

let uu____16004 = (

let uu____16009 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____16009), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16004))
in ((((l_imp_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16003)))
in (FStar_SMTEncoding_Util.mkForall uu____15992))
in ((uu____15991), (FStar_Pervasives_Native.Some ("==> interpretation")), ("l_imp-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____15984))
in (uu____15983)::[]))))))))))
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

let uu____16072 = (

let uu____16073 = (

let uu____16080 = (

let uu____16081 = (

let uu____16092 = (

let uu____16093 = (

let uu____16098 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____16098), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16093))
in ((((l_iff_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16092)))
in (FStar_SMTEncoding_Util.mkForall uu____16081))
in ((uu____16080), (FStar_Pervasives_Native.Some ("<==> interpretation")), ("l_iff-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16073))
in (uu____16072)::[]))))))))))
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

let uu____16150 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16150))
in (

let uu____16153 = (

let uu____16154 = (

let uu____16161 = (

let uu____16162 = (

let uu____16173 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((l_not_a)::[])::[]), ((aa)::[]), (uu____16173)))
in (FStar_SMTEncoding_Util.mkForall uu____16162))
in ((uu____16161), (FStar_Pervasives_Native.Some ("not interpretation")), ("l_not-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16154))
in (uu____16153)::[])))))))
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

let uu____16233 = (

let uu____16240 = (

let uu____16243 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____16243)::[])
in (("Valid"), (uu____16240)))
in (FStar_SMTEncoding_Util.mkApp uu____16233))
in (

let uu____16246 = (

let uu____16247 = (

let uu____16254 = (

let uu____16255 = (

let uu____16266 = (

let uu____16267 = (

let uu____16272 = (

let uu____16273 = (

let uu____16284 = (

let uu____16289 = (

let uu____16292 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____16292)::[])
in (uu____16289)::[])
in (

let uu____16297 = (

let uu____16298 = (

let uu____16303 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____16303), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____16298))
in ((uu____16284), ((xx1)::[]), (uu____16297))))
in (FStar_SMTEncoding_Util.mkForall uu____16273))
in ((uu____16272), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16267))
in ((((l_forall_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16266)))
in (FStar_SMTEncoding_Util.mkForall uu____16255))
in ((uu____16254), (FStar_Pervasives_Native.Some ("forall interpretation")), ("forall-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16247))
in (uu____16246)::[])))))))))))
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

let uu____16385 = (

let uu____16392 = (

let uu____16395 = (FStar_SMTEncoding_Util.mk_ApplyTT b x1)
in (uu____16395)::[])
in (("Valid"), (uu____16392)))
in (FStar_SMTEncoding_Util.mkApp uu____16385))
in (

let uu____16398 = (

let uu____16399 = (

let uu____16406 = (

let uu____16407 = (

let uu____16418 = (

let uu____16419 = (

let uu____16424 = (

let uu____16425 = (

let uu____16436 = (

let uu____16441 = (

let uu____16444 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in (uu____16444)::[])
in (uu____16441)::[])
in (

let uu____16449 = (

let uu____16450 = (

let uu____16455 = (FStar_SMTEncoding_Term.mk_HasTypeZ x1 a)
in ((uu____16455), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____16450))
in ((uu____16436), ((xx1)::[]), (uu____16449))))
in (FStar_SMTEncoding_Util.mkExists uu____16425))
in ((uu____16424), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____16419))
in ((((l_exists_a_b)::[])::[]), ((aa)::(bb)::[]), (uu____16418)))
in (FStar_SMTEncoding_Util.mkForall uu____16407))
in ((uu____16406), (FStar_Pervasives_Native.Some ("exists interpretation")), ("exists-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16399))
in (uu____16398)::[])))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____16515 = (

let uu____16516 = (

let uu____16523 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (

let uu____16524 = (varops.mk_unique "typing_range_const")
in ((uu____16523), (FStar_Pervasives_Native.Some ("Range_const typing")), (uu____16524))))
in (FStar_SMTEncoding_Util.mkAssume uu____16516))
in (uu____16515)::[])))
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

let uu____16558 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1"))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16558 x1 t))
in (

let uu____16559 = (

let uu____16570 = (FStar_SMTEncoding_Util.mkImp ((hastypeZ), (hastypeS)))
in ((((hastypeZ)::[])::[]), ((xx1)::[]), (uu____16570)))
in (FStar_SMTEncoding_Util.mkForall uu____16559))))
in (

let uu____16593 = (

let uu____16594 = (

let uu____16601 = (

let uu____16602 = (

let uu____16613 = (FStar_SMTEncoding_Util.mkImp ((valid), (body)))
in ((((inversion_t)::[])::[]), ((tt1)::[]), (uu____16613)))
in (FStar_SMTEncoding_Util.mkForall uu____16602))
in ((uu____16601), (FStar_Pervasives_Native.Some ("inversion interpretation")), ("inversion-interp")))
in (FStar_SMTEncoding_Util.mkAssume uu____16594))
in (uu____16593)::[])))))))))
in (

let prims1 = (((FStar_Parser_Const.unit_lid), (mk_unit)))::(((FStar_Parser_Const.bool_lid), (mk_bool)))::(((FStar_Parser_Const.int_lid), (mk_int)))::(((FStar_Parser_Const.string_lid), (mk_str)))::(((FStar_Parser_Const.true_lid), (mk_true_interp)))::(((FStar_Parser_Const.false_lid), (mk_false_interp)))::(((FStar_Parser_Const.and_lid), (mk_and_interp)))::(((FStar_Parser_Const.or_lid), (mk_or_interp)))::(((FStar_Parser_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Parser_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Parser_Const.imp_lid), (mk_imp_interp)))::(((FStar_Parser_Const.iff_lid), (mk_iff_interp)))::(((FStar_Parser_Const.not_lid), (mk_not_interp)))::(((FStar_Parser_Const.forall_lid), (mk_forall_interp)))::(((FStar_Parser_Const.exists_lid), (mk_exists_interp)))::(((FStar_Parser_Const.range_lid), (mk_range_interp)))::(((FStar_Parser_Const.inversion_lid), (mk_inversion_axiom)))::[]
in (fun env t s tt -> (

let uu____16937 = (FStar_Util.find_opt (fun uu____16963 -> (match (uu____16963) with
| (l, uu____16975) -> begin
(FStar_Ident.lid_equals l t)
end)) prims1)
in (match (uu____16937) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (uu____17000, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____17039 = (encode_function_type_as_formula t env)
in (match (uu____17039) with
| (form, decls) -> begin
(FStar_List.append decls (((FStar_SMTEncoding_Util.mkAssume ((form), (FStar_Pervasives_Native.Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), ((Prims.strcat "lemma_" lid.FStar_Ident.str)))))::[]))
end))))


let encode_free_var : Prims.bool  ->  env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun uninterpreted env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____17085 = (((

let uu____17088 = ((FStar_Syntax_Util.is_pure_or_ghost_function t_norm) || (FStar_TypeChecker_Env.is_reifiable_function env.tcenv t_norm))
in (FStar_All.pipe_left Prims.op_Negation uu____17088)) || (FStar_Syntax_Util.is_lemma t_norm)) || uninterpreted)
in (match (uu____17085) with
| true -> begin
(

let uu____17095 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____17095) with
| (vname, vtok, env1) -> begin
(

let arg_sorts = (

let uu____17114 = (

let uu____17115 = (FStar_Syntax_Subst.compress t_norm)
in uu____17115.FStar_Syntax_Syntax.n)
in (match (uu____17114) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____17121) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____17151 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____17156 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env1)))))
end))
end
| uu____17169 -> begin
(

let uu____17170 = (prims.is lid)
in (match (uu____17170) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____17178 = (prims.mk lid vname)
in (match (uu____17178) with
| (tok, definition) -> begin
(

let env1 = (push_free_var env lid vname (FStar_Pervasives_Native.Some (tok)))
in ((definition), (env1)))
end)))
end
| uu____17200 -> begin
(

let encode_non_total_function_typ = (Prims.op_disEquality lid.FStar_Ident.nsstr "Prims")
in (

let uu____17202 = (

let uu____17213 = (curried_arrow_formals_comp t_norm)
in (match (uu____17213) with
| (args, comp) -> begin
(

let comp1 = (

let uu____17231 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv comp)
in (match (uu____17231) with
| true -> begin
(

let uu____17232 = (FStar_TypeChecker_Env.reify_comp (

let uu___149_17235 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___149_17235.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___149_17235.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___149_17235.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___149_17235.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___149_17235.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___149_17235.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___149_17235.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___149_17235.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___149_17235.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___149_17235.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___149_17235.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___149_17235.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___149_17235.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___149_17235.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___149_17235.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___149_17235.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___149_17235.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___149_17235.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___149_17235.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___149_17235.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___149_17235.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___149_17235.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___149_17235.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___149_17235.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___149_17235.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___149_17235.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___149_17235.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___149_17235.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___149_17235.FStar_TypeChecker_Env.identifier_info}) comp FStar_Syntax_Syntax.U_unknown)
in (FStar_Syntax_Syntax.mk_Total uu____17232))
end
| uu____17236 -> begin
comp
end))
in (match (encode_non_total_function_typ) with
| true -> begin
(

let uu____17247 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp1)
in ((args), (uu____17247)))
end
| uu____17260 -> begin
((args), (((FStar_Pervasives_Native.None), ((FStar_Syntax_Util.comp_result comp1)))))
end))
end))
in (match (uu____17202) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____17292 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____17292) with
| (vname, vtok, env1) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____17313 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___121_17355 -> (match (uu___121_17355) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____17359 = (FStar_Util.prefix vars)
in (match (uu____17359) with
| (uu____17380, (xxsym, uu____17382)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____17400 = (

let uu____17401 = (

let uu____17408 = (

let uu____17409 = (

let uu____17420 = (

let uu____17421 = (

let uu____17426 = (

let uu____17427 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____17427))
in ((vapp), (uu____17426)))
in (FStar_SMTEncoding_Util.mkEq uu____17421))
in ((((vapp)::[])::[]), (vars), (uu____17420)))
in (FStar_SMTEncoding_Util.mkForall uu____17409))
in ((uu____17408), (FStar_Pervasives_Native.Some ("Discriminator equation")), ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str)))))
in (FStar_SMTEncoding_Util.mkAssume uu____17401))
in (uu____17400)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____17446 = (FStar_Util.prefix vars)
in (match (uu____17446) with
| (uu____17467, (xxsym, uu____17469)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f1 = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f1)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____17492 = (

let uu____17493 = (

let uu____17500 = (

let uu____17501 = (

let uu____17512 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____17512)))
in (FStar_SMTEncoding_Util.mkForall uu____17501))
in ((uu____17500), (FStar_Pervasives_Native.Some ("Projector equation")), ((Prims.strcat "proj_equation_" tp_name))))
in (FStar_SMTEncoding_Util.mkAssume uu____17493))
in (uu____17492)::[])))))
end))
end
| uu____17529 -> begin
[]
end)))))
in (

let uu____17530 = (encode_binders FStar_Pervasives_Native.None formals env1)
in (match (uu____17530) with
| (vars, guards, env', decls1, uu____17557) -> begin
(

let uu____17570 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17579 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____17579), (decls1)))
end
| FStar_Pervasives_Native.Some (p) -> begin
(

let uu____17581 = (encode_formula p env')
in (match (uu____17581) with
| (g, ds) -> begin
(

let uu____17592 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____17592), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____17570) with
| (guard, decls11) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____17605 = (

let uu____17612 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____17612)))
in (FStar_SMTEncoding_Util.mkApp uu____17605))
in (

let uu____17621 = (

let vname_decl = (

let uu____17629 = (

let uu____17640 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____17650 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____17640), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____17629))
in (

let uu____17659 = (

let env2 = (

let uu___150_17665 = env1
in {bindings = uu___150_17665.bindings; depth = uu___150_17665.depth; tcenv = uu___150_17665.tcenv; warn = uu___150_17665.warn; cache = uu___150_17665.cache; nolabels = uu___150_17665.nolabels; use_zfuel_name = uu___150_17665.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ; current_module_name = uu___150_17665.current_module_name})
in (

let uu____17666 = (

let uu____17667 = (head_normal env2 tt)
in (not (uu____17667)))
in (match (uu____17666) with
| true -> begin
(encode_term_pred FStar_Pervasives_Native.None tt env2 vtok_tm)
end
| uu____17672 -> begin
(encode_term_pred FStar_Pervasives_Native.None t_norm env2 vtok_tm)
end)))
in (match (uu____17659) with
| (tok_typing, decls2) -> begin
(

let tok_typing1 = (match (formals) with
| (uu____17682)::uu____17683 -> begin
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

let uu____17723 = (

let uu____17734 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____17734)))
in (FStar_SMTEncoding_Util.mkForall uu____17723))
in (FStar_SMTEncoding_Util.mkAssume ((guarded_tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname)))))))))
end
| uu____17761 -> begin
(FStar_SMTEncoding_Util.mkAssume ((tok_typing), (FStar_Pervasives_Native.Some ("function token typing")), ((Prims.strcat "function_token_typing_" vname))))
end)
in (

let uu____17764 = (match (formals) with
| [] -> begin
(

let uu____17781 = (

let uu____17782 = (

let uu____17785 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_43 -> FStar_Pervasives_Native.Some (_0_43)) uu____17785))
in (push_free_var env1 lid vname uu____17782))
in (((FStar_List.append decls2 ((tok_typing1)::[]))), (uu____17781)))
end
| uu____17790 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let vtok_fresh = (

let uu____17797 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) uu____17797))
in (

let name_tok_corr = (

let uu____17799 = (

let uu____17806 = (

let uu____17807 = (

let uu____17818 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____17818)))
in (FStar_SMTEncoding_Util.mkForall uu____17807))
in ((uu____17806), (FStar_Pervasives_Native.Some ("Name-token correspondence")), ((Prims.strcat "token_correspondence_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____17799))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing1)::[]))), (env1)))))
end)
in (match (uu____17764) with
| (tok_decl, env2) -> begin
(((vname_decl)::tok_decl), (env2))
end)))
end)))
in (match (uu____17621) with
| (decls2, env2) -> begin
(

let uu____17861 = (

let res_t1 = (FStar_Syntax_Subst.compress res_t)
in (

let uu____17869 = (encode_term res_t1 env')
in (match (uu____17869) with
| (encoded_res_t, decls) -> begin
(

let uu____17882 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____17882), (decls)))
end)))
in (match (uu____17861) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____17893 = (

let uu____17900 = (

let uu____17901 = (

let uu____17912 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____17912)))
in (FStar_SMTEncoding_Util.mkForall uu____17901))
in ((uu____17900), (FStar_Pervasives_Native.Some ("free var typing")), ((Prims.strcat "typing_" vname))))
in (FStar_SMTEncoding_Util.mkAssume uu____17893))
in (

let freshness = (

let uu____17928 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____17928) with
| true -> begin
(

let uu____17933 = (

let uu____17934 = (

let uu____17945 = (FStar_All.pipe_right vars (FStar_List.map FStar_Pervasives_Native.snd))
in (

let uu____17956 = (varops.next_id ())
in ((vname), (uu____17945), (FStar_SMTEncoding_Term.Term_sort), (uu____17956))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____17934))
in (

let uu____17959 = (

let uu____17962 = (pretype_axiom env2 vapp vars)
in (uu____17962)::[])
in (uu____17933)::uu____17959))
end
| uu____17963 -> begin
[]
end))
in (

let g = (

let uu____17967 = (

let uu____17970 = (

let uu____17973 = (

let uu____17976 = (

let uu____17979 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____17979)
in (FStar_List.append freshness uu____17976))
in (FStar_List.append decls3 uu____17973))
in (FStar_List.append decls2 uu____17970))
in (FStar_List.append decls11 uu____17967))
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

let uu____18014 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____18014) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18051 = (encode_free_var false env x t t_norm [])
in (match (uu____18051) with
| (decls, env1) -> begin
(

let uu____18078 = (lookup_lid env1 x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____18078) with
| (n1, x', uu____18105) -> begin
((((n1), (x'))), (decls), (env1))
end))
end))
end
| FStar_Pervasives_Native.Some (n1, x1, uu____18126) -> begin
((((n1), (x1))), ([]), (env))
end)))


let encode_top_level_val : Prims.bool  ->  env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun uninterpreted env lid t quals -> (

let tt = (norm env t)
in (

let uu____18186 = (encode_free_var uninterpreted env lid t tt quals)
in (match (uu____18186) with
| (decls, env1) -> begin
(

let uu____18205 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____18205) with
| true -> begin
(

let uu____18212 = (

let uu____18215 = (encode_smt_lemma env1 lid tt)
in (FStar_List.append decls uu____18215))
in ((uu____18212), (env1)))
end
| uu____18220 -> begin
((decls), (env1))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____18270 lb -> (match (uu____18270) with
| (decls, env1) -> begin
(

let uu____18290 = (

let uu____18297 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val false env1 uu____18297 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____18290) with
| (decls', env2) -> begin
(((FStar_List.append decls decls')), (env2))
end))
end)) (([]), (env)))))


let is_tactic : FStar_Syntax_Syntax.term  ->  Prims.bool = (fun t -> (

let fstar_tactics_tactic_lid = (FStar_Parser_Const.p2l (("FStar")::("Tactics")::("tactic")::[]))
in (

let uu____18319 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____18319) with
| (hd1, args) -> begin
(

let uu____18356 = (

let uu____18357 = (FStar_Syntax_Util.un_uinst hd1)
in uu____18357.FStar_Syntax_Syntax.n)
in (match (uu____18356) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid) -> begin
true
end
| FStar_Syntax_Syntax.Tm_arrow (uu____18361, c) -> begin
(

let effect_name = (FStar_Syntax_Util.comp_effect_name c)
in (FStar_Util.starts_with "FStar.Tactics" effect_name.FStar_Ident.str))
end
| uu____18380 -> begin
false
end))
end))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____18405 quals -> (match (uu____18405) with
| (is_rec, bindings) -> begin
(

let eta_expand1 = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____18481 = (FStar_Util.first_N nbinders formals)
in (match (uu____18481) with
| (formals1, extra_formals) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____18562 uu____18563 -> (match (((uu____18562), (uu____18563))) with
| ((formal, uu____18581), (binder, uu____18583)) -> begin
(

let uu____18592 = (

let uu____18599 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____18599)))
in FStar_Syntax_Syntax.NT (uu____18592))
end)) formals1 binders)
in (

let extra_formals1 = (

let uu____18607 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____18638 -> (match (uu____18638) with
| (x, i) -> begin
(

let uu____18649 = (

let uu___151_18650 = x
in (

let uu____18651 = (FStar_Syntax_Subst.subst subst1 x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___151_18650.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___151_18650.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____18651}))
in ((uu____18649), (i)))
end))))
in (FStar_All.pipe_right uu____18607 FStar_Syntax_Util.name_binders))
in (

let body1 = (

let uu____18669 = (

let uu____18670 = (FStar_Syntax_Subst.compress body)
in (

let uu____18671 = (

let uu____18672 = (FStar_Syntax_Util.args_of_binders extra_formals1)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____18672))
in (FStar_Syntax_Syntax.extend_app_n uu____18670 uu____18671)))
in (uu____18669 FStar_Pervasives_Native.None body.FStar_Syntax_Syntax.pos))
in (((FStar_List.append binders extra_formals1)), (body1)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let get_result_type = (fun c -> (

let uu____18733 = (FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c)
in (match (uu____18733) with
| true -> begin
(FStar_TypeChecker_Env.reify_comp (

let uu___152_18736 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___152_18736.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___152_18736.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___152_18736.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___152_18736.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___152_18736.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___152_18736.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___152_18736.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___152_18736.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___152_18736.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___152_18736.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___152_18736.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___152_18736.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___152_18736.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___152_18736.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___152_18736.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___152_18736.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___152_18736.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___152_18736.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___152_18736.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___152_18736.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___152_18736.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.type_of = uu___152_18736.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___152_18736.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___152_18736.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___152_18736.FStar_TypeChecker_Env.qname_and_index; FStar_TypeChecker_Env.proof_ns = uu___152_18736.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth = uu___152_18736.FStar_TypeChecker_Env.synth; FStar_TypeChecker_Env.is_native_tactic = uu___152_18736.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___152_18736.FStar_TypeChecker_Env.identifier_info}) c FStar_Syntax_Syntax.U_unknown)
end
| uu____18737 -> begin
(FStar_Syntax_Util.comp_result c)
end)))
in (

let rec aux = (fun norm1 t_norm1 -> (

let uu____18769 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____18769) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____18833)::uu____18834 -> begin
(

let uu____18849 = (

let uu____18850 = (

let uu____18853 = (FStar_Syntax_Subst.compress t_norm1)
in (FStar_All.pipe_left FStar_Syntax_Util.unascribe uu____18853))
in uu____18850.FStar_Syntax_Syntax.n)
in (match (uu____18849) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____18896 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____18896) with
| (formals1, c1) -> begin
(

let nformals = (FStar_List.length formals1)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (get_result_type c1)
in (

let uu____18938 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c1))
in (match (uu____18938) with
| true -> begin
(

let uu____18973 = (FStar_Util.first_N nformals binders)
in (match (uu____18973) with
| (bs0, rest) -> begin
(

let c2 = (

let subst1 = (FStar_List.map2 (fun uu____19067 uu____19068 -> (match (((uu____19067), (uu____19068))) with
| ((x, uu____19086), (b, uu____19088)) -> begin
(

let uu____19097 = (

let uu____19104 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____19104)))
in FStar_Syntax_Syntax.NT (uu____19097))
end)) formals1 bs0)
in (FStar_Syntax_Subst.subst_comp subst1 c1))
in (

let body1 = (FStar_Syntax_Util.abs rest body lopt)
in (

let uu____19106 = (

let uu____19127 = (get_result_type c2)
in ((bs0), (body1), (bs0), (uu____19127)))
in ((uu____19106), (false)))))
end))
end
| uu____19160 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____19195 = (eta_expand1 binders formals1 body tres)
in (match (uu____19195) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end))
end
| uu____19274 -> begin
((((binders), (body), (formals1), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____19284) -> begin
(

let uu____19289 = (

let uu____19310 = (aux norm1 x.FStar_Syntax_Syntax.sort)
in (FStar_Pervasives_Native.fst uu____19310))
in ((uu____19289), (true)))
end
| uu____19375 when (not (norm1)) -> begin
(

let t_norm2 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm1)
in (aux true t_norm2))
end
| uu____19377 -> begin
(

let uu____19378 = (

let uu____19379 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____19380 = (FStar_Syntax_Print.term_to_string t_norm1)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____19379 uu____19380)))
in (failwith uu____19378))
end))
end
| uu____19405 -> begin
(

let uu____19406 = (

let uu____19407 = (FStar_Syntax_Subst.compress t_norm1)
in uu____19407.FStar_Syntax_Syntax.n)
in (match (uu____19406) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____19452 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____19452) with
| (formals1, c1) -> begin
(

let tres = (get_result_type c1)
in (

let uu____19484 = (eta_expand1 [] formals1 e tres)
in (match (uu____19484) with
| (binders1, body1) -> begin
((((binders1), (body1), (formals1), (tres))), (false))
end)))
end))
end
| uu____19567 -> begin
(((([]), (e), ([]), (t_norm1))), (false))
end))
end)
end)))
in (aux false t_norm))))
in (FStar_All.try_with (fun uu___154_19616 -> (match (()) with
| () -> begin
(

let uu____19623 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> ((FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp) || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))))
in (match (uu____19623) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____19634 -> begin
(

let uu____19635 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____19729 lb -> (match (uu____19729) with
| (toks, typs, decls, env1) -> begin
((

let uu____19824 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____19824) with
| true -> begin
(FStar_Exn.raise Let_rec_unencodeable)
end
| uu____19825 -> begin
()
end));
(

let t_norm = (whnf env1 lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____19827 = (

let uu____19842 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env1 uu____19842 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____19827) with
| (tok, decl, env2) -> begin
(

let uu____19888 = (

let uu____19901 = (

let uu____19912 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((uu____19912), (tok)))
in (uu____19901)::toks)
in ((uu____19888), ((t_norm)::typs), ((decl)::decls), (env2)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____19635) with
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
| uu____20095 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| FStar_Pervasives_Native.Some (ftok1) -> begin
(mk_Apply ftok1 vars)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____20103 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____20103 vars))
end)
end
| uu____20104 -> begin
(

let uu____20105 = (

let uu____20112 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____20112)))
in (FStar_SMTEncoding_Util.mkApp uu____20105))
end)
end))
in (

let encode_non_rec_lbdef = (fun bindings1 typs2 toks2 env2 -> (match (((bindings1), (typs2), (toks2))) with
| (({FStar_Syntax_Syntax.lbname = uu____20194; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____20196; FStar_Syntax_Syntax.lbeff = uu____20197; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____20260 = (

let uu____20267 = (FStar_TypeChecker_Env.open_universes_in env2.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____20267) with
| (tcenv', uu____20285, e_t) -> begin
(

let uu____20291 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____20302 -> begin
(failwith "Impossible")
end)
in (match (uu____20291) with
| (e1, t_norm1) -> begin
(((

let uu___155_20318 = env2
in {bindings = uu___155_20318.bindings; depth = uu___155_20318.depth; tcenv = tcenv'; warn = uu___155_20318.warn; cache = uu___155_20318.cache; nolabels = uu___155_20318.nolabels; use_zfuel_name = uu___155_20318.use_zfuel_name; encode_non_total_function_typ = uu___155_20318.encode_non_total_function_typ; current_module_name = uu___155_20318.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____20260) with
| (env', e1, t_norm1) -> begin
(

let uu____20328 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____20328) with
| ((binders, body, uu____20349, uu____20350), curry) -> begin
((

let uu____20361 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env2.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____20361) with
| true -> begin
(

let uu____20362 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____20363 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____20362 uu____20363)))
end
| uu____20364 -> begin
()
end));
(

let uu____20365 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____20365) with
| (vars, guards, env'1, binder_decls, uu____20392) -> begin
(

let body1 = (

let uu____20406 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____20406) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____20407 -> begin
body
end))
in (

let app = (mk_app1 curry f ftok vars)
in (

let uu____20409 = (

let uu____20418 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____20418) with
| true -> begin
(

let uu____20429 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____20430 = (encode_formula body1 env'1)
in ((uu____20429), (uu____20430))))
end
| uu____20439 -> begin
(

let uu____20440 = (encode_term body1 env'1)
in ((app), (uu____20440)))
end))
in (match (uu____20409) with
| (app1, (body2, decls2)) -> begin
(

let eqn = (

let uu____20463 = (

let uu____20470 = (

let uu____20471 = (

let uu____20482 = (FStar_SMTEncoding_Util.mkEq ((app1), (body2)))
in ((((app1)::[])::[]), (vars), (uu____20482)))
in (FStar_SMTEncoding_Util.mkForall uu____20471))
in (

let uu____20493 = (

let uu____20496 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____20496))
in ((uu____20470), (uu____20493), ((Prims.strcat "equation_" f)))))
in (FStar_SMTEncoding_Util.mkAssume uu____20463))
in (

let uu____20499 = (

let uu____20502 = (

let uu____20505 = (

let uu____20508 = (

let uu____20511 = (primitive_type_axioms env2.tcenv flid f app1)
in (FStar_List.append ((eqn)::[]) uu____20511))
in (FStar_List.append decls2 uu____20508))
in (FStar_List.append binder_decls uu____20505))
in (FStar_List.append decls1 uu____20502))
in ((uu____20499), (env2))))
end))))
end));
)
end))
end)))
end
| uu____20516 -> begin
(failwith "Impossible")
end))
in (

let encode_rec_lbdefs = (fun bindings1 typs2 toks2 env2 -> (

let fuel = (

let uu____20601 = (varops.fresh "fuel")
in ((uu____20601), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env2
in (

let uu____20604 = (FStar_All.pipe_right toks2 (FStar_List.fold_left (fun uu____20692 uu____20693 -> (match (((uu____20692), (uu____20693))) with
| ((gtoks, env3), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (

let uu____20841 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____20841))
in (

let gtok = (

let uu____20843 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____20843))
in (

let env4 = (

let uu____20845 = (

let uu____20848 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_44 -> FStar_Pervasives_Native.Some (_0_44)) uu____20848))
in (push_free_var env3 flid gtok uu____20845))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env4))))))
end)) (([]), (env2))))
in (match (uu____20604) with
| (gtoks, env3) -> begin
(

let gtoks1 = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env01 uu____21004 t_norm uu____21006 -> (match (((uu____21004), (uu____21006))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____21050; FStar_Syntax_Syntax.lbeff = uu____21051; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let uu____21079 = (

let uu____21086 = (FStar_TypeChecker_Env.open_universes_in env3.tcenv uvs ((e)::(t_norm)::[]))
in (match (uu____21086) with
| (tcenv', uu____21108, e_t) -> begin
(

let uu____21114 = (match (e_t) with
| (e1)::(t_norm1)::[] -> begin
((e1), (t_norm1))
end
| uu____21125 -> begin
(failwith "Impossible")
end)
in (match (uu____21114) with
| (e1, t_norm1) -> begin
(((

let uu___156_21141 = env3
in {bindings = uu___156_21141.bindings; depth = uu___156_21141.depth; tcenv = tcenv'; warn = uu___156_21141.warn; cache = uu___156_21141.cache; nolabels = uu___156_21141.nolabels; use_zfuel_name = uu___156_21141.use_zfuel_name; encode_non_total_function_typ = uu___156_21141.encode_non_total_function_typ; current_module_name = uu___156_21141.current_module_name})), (e1), (t_norm1))
end))
end))
in (match (uu____21079) with
| (env', e1, t_norm1) -> begin
((

let uu____21156 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____21156) with
| true -> begin
(

let uu____21157 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____21158 = (FStar_Syntax_Print.term_to_string t_norm1)
in (

let uu____21159 = (FStar_Syntax_Print.term_to_string e1)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____21157 uu____21158 uu____21159))))
end
| uu____21160 -> begin
()
end));
(

let uu____21161 = (destruct_bound_function flid t_norm1 e1)
in (match (uu____21161) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____21198 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env01.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____21198) with
| true -> begin
(

let uu____21199 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____21200 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____21201 = (FStar_Syntax_Print.binders_to_string ", " formals)
in (

let uu____21202 = (FStar_Syntax_Print.term_to_string tres)
in (FStar_Util.print4 "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n" uu____21199 uu____21200 uu____21201 uu____21202)))))
end
| uu____21203 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____21205 -> begin
()
end);
(

let uu____21206 = (encode_binders FStar_Pervasives_Native.None binders env')
in (match (uu____21206) with
| (vars, guards, env'1, binder_decls, uu____21237) -> begin
(

let decl_g = (

let uu____21251 = (

let uu____21262 = (

let uu____21265 = (FStar_List.map FStar_Pervasives_Native.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____21265)
in ((g), (uu____21262), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____21251))
in (

let env02 = (push_zfuel_name env01 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____21290 = (

let uu____21297 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____21297)))
in (FStar_SMTEncoding_Util.mkApp uu____21290))
in (

let gsapp = (

let uu____21307 = (

let uu____21314 = (

let uu____21317 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____21317)::vars_tm)
in ((g), (uu____21314)))
in (FStar_SMTEncoding_Util.mkApp uu____21307))
in (

let gmax = (

let uu____21323 = (

let uu____21330 = (

let uu____21333 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____21333)::vars_tm)
in ((g), (uu____21330)))
in (FStar_SMTEncoding_Util.mkApp uu____21323))
in (

let body1 = (

let uu____21339 = (FStar_TypeChecker_Env.is_reifiable_function env'1.tcenv t_norm1)
in (match (uu____21339) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env'1.tcenv body)
end
| uu____21340 -> begin
body
end))
in (

let uu____21341 = (encode_term body1 env'1)
in (match (uu____21341) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____21359 = (

let uu____21366 = (

let uu____21367 = (

let uu____21382 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____21382)))
in (FStar_SMTEncoding_Util.mkForall' uu____21367))
in (

let uu____21403 = (

let uu____21406 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in FStar_Pervasives_Native.Some (uu____21406))
in ((uu____21366), (uu____21403), ((Prims.strcat "equation_with_fuel_" g)))))
in (FStar_SMTEncoding_Util.mkAssume uu____21359))
in (

let eqn_f = (

let uu____21410 = (

let uu____21417 = (

let uu____21418 = (

let uu____21429 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____21429)))
in (FStar_SMTEncoding_Util.mkForall uu____21418))
in ((uu____21417), (FStar_Pervasives_Native.Some ("Correspondence of recursive function to instrumented version")), ((Prims.strcat "@fuel_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21410))
in (

let eqn_g' = (

let uu____21443 = (

let uu____21450 = (

let uu____21451 = (

let uu____21462 = (

let uu____21463 = (

let uu____21468 = (

let uu____21469 = (

let uu____21476 = (

let uu____21479 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____21479)::vars_tm)
in ((g), (uu____21476)))
in (FStar_SMTEncoding_Util.mkApp uu____21469))
in ((gsapp), (uu____21468)))
in (FStar_SMTEncoding_Util.mkEq uu____21463))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____21462)))
in (FStar_SMTEncoding_Util.mkForall uu____21451))
in ((uu____21450), (FStar_Pervasives_Native.Some ("Fuel irrelevance")), ((Prims.strcat "@fuel_irrelevance_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21443))
in (

let uu____21502 = (

let uu____21511 = (encode_binders FStar_Pervasives_Native.None formals env02)
in (match (uu____21511) with
| (vars1, v_guards, env4, binder_decls1, uu____21540) -> begin
(

let vars_tm1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars1)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm1)))
in (

let tok_corr = (

let tok_app = (

let uu____21565 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____21565 ((fuel)::vars1)))
in (

let uu____21570 = (

let uu____21577 = (

let uu____21578 = (

let uu____21589 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars1), (uu____21589)))
in (FStar_SMTEncoding_Util.mkForall uu____21578))
in ((uu____21577), (FStar_Pervasives_Native.Some ("Fuel token correspondence")), ((Prims.strcat "fuel_token_correspondence_" gtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____21570)))
in (

let uu____21610 = (

let uu____21617 = (encode_term_pred FStar_Pervasives_Native.None tres env4 gapp)
in (match (uu____21617) with
| (g_typing, d3) -> begin
(

let uu____21630 = (

let uu____21633 = (

let uu____21634 = (

let uu____21641 = (

let uu____21642 = (

let uu____21653 = (

let uu____21654 = (

let uu____21659 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____21659), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____21654))
in ((((gapp)::[])::[]), ((fuel)::vars1), (uu____21653)))
in (FStar_SMTEncoding_Util.mkForall uu____21642))
in ((uu____21641), (FStar_Pervasives_Native.Some ("Typing correspondence of token to term")), ((Prims.strcat "token_correspondence_" g))))
in (FStar_SMTEncoding_Util.mkAssume uu____21634))
in (uu____21633)::[])
in ((d3), (uu____21630)))
end))
in (match (uu____21610) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls1 aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____21502) with
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

let uu____21724 = (

let uu____21737 = (FStar_List.zip3 gtoks1 typs2 bindings1)
in (FStar_List.fold_left (fun uu____21816 uu____21817 -> (match (((uu____21816), (uu____21817))) with
| ((decls2, eqns, env01), (gtok, ty, lb)) -> begin
(

let uu____21972 = (encode_one_binding env01 gtok ty lb)
in (match (uu____21972) with
| (decls', eqns', env02) -> begin
(((decls')::decls2), ((FStar_List.append eqns' eqns)), (env02))
end))
end)) (((decls1)::[]), ([]), (env0)) uu____21737))
in (match (uu____21724) with
| (decls2, eqns, env01) -> begin
(

let uu____22045 = (

let isDeclFun = (fun uu___122_22057 -> (match (uu___122_22057) with
| FStar_SMTEncoding_Term.DeclFun (uu____22058) -> begin
true
end
| uu____22069 -> begin
false
end))
in (

let uu____22070 = (FStar_All.pipe_right decls2 FStar_List.flatten)
in (FStar_All.pipe_right uu____22070 (FStar_List.partition isDeclFun))))
in (match (uu____22045) with
| (prefix_decls, rest) -> begin
(

let eqns1 = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns1))), (env01)))
end))
end))))
end))))))
in (

let uu____22110 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___123_22114 -> (match (uu___123_22114) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____22115 -> begin
false
end)))) || (FStar_All.pipe_right typs1 (FStar_Util.for_some (fun t -> (

let uu____22121 = ((FStar_Syntax_Util.is_pure_or_ghost_function t) || (FStar_TypeChecker_Env.is_reifiable_function env1.tcenv t))
in (FStar_All.pipe_left Prims.op_Negation uu____22121))))))
in (match (uu____22110) with
| true -> begin
((decls1), (env1))
end
| uu____22130 -> begin
(FStar_All.try_with (fun uu___158_22138 -> (match (()) with
| () -> begin
(match ((not (is_rec))) with
| true -> begin
(encode_non_rec_lbdef bindings typs1 toks1 env1)
end
| uu____22151 -> begin
(encode_rec_lbdefs bindings typs1 toks1 env1)
end)
end)) (fun uu___157_22153 -> (match (uu___157_22153) with
| Inner_let_rec -> begin
((decls1), (env1))
end)))
end))))))))
end))
end))
end)) (fun uu___153_22165 -> (match (uu___153_22165) with
| Let_rec_unencodeable -> begin
(

let msg = (

let uu____22173 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____22173 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end)))))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let nm = (

let uu____22222 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____22222) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____22226 = (encode_sigelt' env se)
in (match (uu____22226) with
| (g, env1) -> begin
(

let g1 = (match (g) with
| [] -> begin
(

let uu____22242 = (

let uu____22243 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____22243))
in (uu____22242)::[])
end
| uu____22244 -> begin
(

let uu____22245 = (

let uu____22248 = (

let uu____22249 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____22249))
in (uu____22248)::g)
in (

let uu____22250 = (

let uu____22253 = (

let uu____22254 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____22254))
in (uu____22253)::[])
in (FStar_List.append uu____22245 uu____22250)))
end)
in ((g1), (env1)))
end))))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let is_opaque_to_smt = (fun t -> (

let uu____22267 = (

let uu____22268 = (FStar_Syntax_Subst.compress t)
in uu____22268.FStar_Syntax_Syntax.n)
in (match (uu____22267) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____22272)) -> begin
(Prims.op_Equality s "opaque_to_smt")
end
| uu____22273 -> begin
false
end)))
in (

let is_uninterpreted_by_smt = (fun t -> (

let uu____22278 = (

let uu____22279 = (FStar_Syntax_Subst.compress t)
in uu____22279.FStar_Syntax_Syntax.n)
in (match (uu____22278) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____22283)) -> begin
(Prims.op_Equality s "uninterpreted_by_smt")
end
| uu____22284 -> begin
false
end)))
in (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____22289) -> begin
(failwith "impossible -- removed by tc.fs")
end
| FStar_Syntax_Syntax.Sig_pragma (uu____22294) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_main (uu____22297) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (uu____22300) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_sub_effect (uu____22315) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let uu____22319 = (

let uu____22320 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____22320 Prims.op_Negation))
in (match (uu____22319) with
| true -> begin
(([]), (env))
end
| uu____22329 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____22346 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((ed.FStar_Syntax_Syntax.binders), (tm), (FStar_Pervasives_Native.Some ((FStar_Syntax_Util.mk_residual_comp FStar_Parser_Const.effect_Tot_lid FStar_Pervasives_Native.None ((FStar_Syntax_Syntax.TOTAL)::[]))))))) FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)
end))
in (

let encode_action = (fun env1 a -> (

let uu____22366 = (new_term_constant_and_tok_from_lid env1 a.FStar_Syntax_Syntax.action_name)
in (match (uu____22366) with
| (aname, atok, env2) -> begin
(

let uu____22382 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____22382) with
| (formals, uu____22400) -> begin
(

let uu____22413 = (

let uu____22418 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____22418 env2))
in (match (uu____22413) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____22430 = (

let uu____22431 = (

let uu____22442 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____22458 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____22442), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____22431))
in (uu____22430)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Action token")))))::[])
in (

let uu____22471 = (

let aux = (fun uu____22523 uu____22524 -> (match (((uu____22523), (uu____22524))) with
| ((bv, uu____22576), (env3, acc_sorts, acc)) -> begin
(

let uu____22614 = (gen_term_var env3 bv)
in (match (uu____22614) with
| (xxsym, xx, env4) -> begin
((env4), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::acc_sorts), ((xx)::acc))
end))
end))
in (FStar_List.fold_right aux formals ((env2), ([]), ([]))))
in (match (uu____22471) with
| (uu____22686, xs_sorts, xs) -> begin
(

let app = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (

let a_eq = (

let uu____22709 = (

let uu____22716 = (

let uu____22717 = (

let uu____22728 = (

let uu____22729 = (

let uu____22734 = (mk_Apply tm xs_sorts)
in ((app), (uu____22734)))
in (FStar_SMTEncoding_Util.mkEq uu____22729))
in ((((app)::[])::[]), (xs_sorts), (uu____22728)))
in (FStar_SMTEncoding_Util.mkForall uu____22717))
in ((uu____22716), (FStar_Pervasives_Native.Some ("Action equality")), ((Prims.strcat aname "_equality"))))
in (FStar_SMTEncoding_Util.mkAssume uu____22709))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____22754 = (

let uu____22761 = (

let uu____22762 = (

let uu____22773 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____22773)))
in (FStar_SMTEncoding_Util.mkForall uu____22762))
in ((uu____22761), (FStar_Pervasives_Native.Some ("Action token correspondence")), ((Prims.strcat aname "_token_correspondence"))))
in (FStar_SMTEncoding_Util.mkAssume uu____22754))))
in ((env2), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____22792 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____22792) with
| (env1, decls2) -> begin
(((FStar_List.flatten decls2)), (env1))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22820, uu____22821) when (FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid) -> begin
(

let uu____22822 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____22822) with
| (tname, ttok, env1) -> begin
(([]), (env1))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22839, t) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let will_encode_definition = (

let uu____22845 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___124_22849 -> (match (uu___124_22849) with
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| FStar_Syntax_Syntax.Projector (uu____22850) -> begin
true
end
| FStar_Syntax_Syntax.Discriminator (uu____22855) -> begin
true
end
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____22856 -> begin
false
end))))
in (not (uu____22845)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____22863 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____22865 = (

let uu____22872 = (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_uninterpreted_by_smt))
in (encode_top_level_val uu____22872 env fv t quals))
in (match (uu____22865) with
| (decls, env1) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____22887 = (

let uu____22890 = (primitive_type_axioms env1.tcenv lid tname tsym)
in (FStar_List.append decls uu____22890))
in ((uu____22887), (env1)))))
end)))
end)))
end
| FStar_Syntax_Syntax.Sig_assume (l, us, f) -> begin
(

let uu____22898 = (FStar_Syntax_Subst.open_univ_vars us f)
in (match (uu____22898) with
| (uu____22907, f1) -> begin
(

let uu____22909 = (encode_formula f1 env)
in (match (uu____22909) with
| (f2, decls) -> begin
(

let g = (

let uu____22923 = (

let uu____22924 = (

let uu____22931 = (

let uu____22934 = (

let uu____22935 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____22935))
in FStar_Pervasives_Native.Some (uu____22934))
in (

let uu____22936 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in ((f2), (uu____22931), (uu____22936))))
in (FStar_SMTEncoding_Util.mkAssume uu____22924))
in (uu____22923)::[])
in (((FStar_List.append decls g)), (env)))
end))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, uu____22942) when ((FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) || (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs (FStar_Util.for_some is_opaque_to_smt))) -> begin
(

let attrs = se.FStar_Syntax_Syntax.sigattrs
in (

let uu____22954 = (FStar_Util.fold_map (fun env1 lb -> (

let lid = (

let uu____22972 = (

let uu____22975 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____22975.FStar_Syntax_Syntax.fv_name)
in uu____22972.FStar_Syntax_Syntax.v)
in (

let uu____22976 = (

let uu____22977 = (FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____22977))
in (match (uu____22976) with
| true -> begin
(

let val_decl = (

let uu___159_23005 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = uu___159_23005.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Irreducible)::se.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___159_23005.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___159_23005.FStar_Syntax_Syntax.sigattrs})
in (

let uu____23010 = (encode_sigelt' env1 val_decl)
in (match (uu____23010) with
| (decls, env2) -> begin
((env2), (decls))
end)))
end
| uu____23021 -> begin
((env1), ([]))
end)))) env (FStar_Pervasives_Native.snd lbs))
in (match (uu____22954) with
| (env1, decls) -> begin
(((FStar_List.flatten decls)), (env1))
end)))
end
| FStar_Syntax_Syntax.Sig_let ((uu____23038, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t1); FStar_Syntax_Syntax.lbunivs = uu____23040; FStar_Syntax_Syntax.lbtyp = uu____23041; FStar_Syntax_Syntax.lbeff = uu____23042; FStar_Syntax_Syntax.lbdef = uu____23043})::[]), uu____23044) when (FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid) -> begin
(

let uu____23063 = (new_term_constant_and_tok_from_lid env b2t1.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____23063) with
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

let uu____23092 = (

let uu____23095 = (

let uu____23096 = (

let uu____23103 = (

let uu____23104 = (

let uu____23115 = (

let uu____23116 = (

let uu____23121 = (FStar_SMTEncoding_Util.mkApp (((FStar_Pervasives_Native.snd FStar_SMTEncoding_Term.boxBoolFun)), ((x)::[])))
in ((valid_b2t_x), (uu____23121)))
in (FStar_SMTEncoding_Util.mkEq uu____23116))
in ((((b2t_x)::[])::[]), ((xx)::[]), (uu____23115)))
in (FStar_SMTEncoding_Util.mkForall uu____23104))
in ((uu____23103), (FStar_Pervasives_Native.Some ("b2t def")), ("b2t_def")))
in (FStar_SMTEncoding_Util.mkAssume uu____23096))
in (uu____23095)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None))))::uu____23092)
in ((decls), (env1)))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____23154, uu____23155) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___125_23164 -> (match (uu___125_23164) with
| FStar_Syntax_Syntax.Discriminator (uu____23165) -> begin
true
end
| uu____23166 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____23169, lids) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____23180 = (

let uu____23181 = (FStar_List.hd l.FStar_Ident.ns)
in uu____23181.FStar_Ident.idText)
in (Prims.op_Equality uu____23180 "Prims"))))) && (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___126_23185 -> (match (uu___126_23185) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____23186 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____23190) when (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals (FStar_Util.for_some (fun uu___127_23207 -> (match (uu___127_23207) with
| FStar_Syntax_Syntax.Projector (uu____23208) -> begin
true
end
| uu____23213 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____23216 = (try_lookup_free_var env l)
in (match (uu____23216) with
| FStar_Pervasives_Native.Some (uu____23223) -> begin
(([]), (env))
end
| FStar_Pervasives_Native.None -> begin
(

let se1 = (

let uu___160_23227 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l); FStar_Syntax_Syntax.sigquals = uu___160_23227.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___160_23227.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___160_23227.FStar_Syntax_Syntax.sigattrs})
in (encode_sigelt env se1))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____23234) -> begin
(encode_top_level_let env ((is_rec), (bindings)) se.FStar_Syntax_Syntax.sigquals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____23252) -> begin
(

let uu____23261 = (encode_sigelts env ses)
in (match (uu____23261) with
| (g, env1) -> begin
(

let uu____23278 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___128_23301 -> (match (uu___128_23301) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = uu____23302; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("inversion axiom"); FStar_SMTEncoding_Term.assumption_name = uu____23303; FStar_SMTEncoding_Term.assumption_fact_ids = uu____23304}) -> begin
false
end
| uu____23307 -> begin
true
end))))
in (match (uu____23278) with
| (g', inversions) -> begin
(

let uu____23322 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___129_23343 -> (match (uu___129_23343) with
| FStar_SMTEncoding_Term.DeclFun (uu____23344) -> begin
true
end
| uu____23355 -> begin
false
end))))
in (match (uu____23322) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env1))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____23373, tps, k, uu____23376, datas) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___130_23393 -> (match (uu___130_23393) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| FStar_Syntax_Syntax.Assumption -> begin
true
end
| uu____23394 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____23403 = c
in (match (uu____23403) with
| (name, args, uu____23408, uu____23409, uu____23410) -> begin
(

let uu____23415 = (

let uu____23416 = (

let uu____23427 = (FStar_All.pipe_right args (FStar_List.map (fun uu____23444 -> (match (uu____23444) with
| (uu____23451, sort, uu____23453) -> begin
sort
end))))
in ((name), (uu____23427), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in FStar_SMTEncoding_Term.DeclFun (uu____23416))
in (uu____23415)::[])
end))
end
| uu____23458 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____23480 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____23486 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____23486 FStar_Option.isNone)))))
in (match (uu____23480) with
| true -> begin
[]
end
| uu____23517 -> begin
(

let uu____23518 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____23518) with
| (xxsym, xx) -> begin
(

let uu____23527 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____23566 l -> (match (uu____23566) with
| (out, decls) -> begin
(

let uu____23586 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____23586) with
| (uu____23597, data_t) -> begin
(

let uu____23599 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____23599) with
| (args, res) -> begin
(

let indices = (

let uu____23645 = (

let uu____23646 = (FStar_Syntax_Subst.compress res)
in uu____23646.FStar_Syntax_Syntax.n)
in (match (uu____23645) with
| FStar_Syntax_Syntax.Tm_app (uu____23657, indices) -> begin
indices
end
| uu____23679 -> begin
[]
end))
in (

let env1 = (FStar_All.pipe_right args (FStar_List.fold_left (fun env1 uu____23703 -> (match (uu____23703) with
| (x, uu____23709) -> begin
(

let uu____23710 = (

let uu____23711 = (

let uu____23718 = (mk_term_projector_name l x)
in ((uu____23718), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____23711))
in (push_term_var env1 x uu____23710))
end)) env))
in (

let uu____23721 = (encode_args indices env1)
in (match (uu____23721) with
| (indices1, decls') -> begin
((match ((Prims.op_disEquality (FStar_List.length indices1) (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____23745 -> begin
()
end);
(

let eqs = (

let uu____23747 = (FStar_List.map2 (fun v1 a -> (

let uu____23763 = (

let uu____23768 = (FStar_SMTEncoding_Util.mkFreeV v1)
in ((uu____23768), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____23763))) vars indices1)
in (FStar_All.pipe_right uu____23747 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____23771 = (

let uu____23772 = (

let uu____23777 = (

let uu____23778 = (

let uu____23783 = (mk_data_tester env1 l xx)
in ((uu____23783), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____23778))
in ((out), (uu____23777)))
in (FStar_SMTEncoding_Util.mkOr uu____23772))
in ((uu____23771), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____23527) with
| (data_ax, decls) -> begin
(

let uu____23796 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____23796) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____23807 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____23807 xx tapp))
end
| uu____23810 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____23811 = (

let uu____23818 = (

let uu____23819 = (

let uu____23830 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____23845 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____23830), (uu____23845))))
in (FStar_SMTEncoding_Util.mkForall uu____23819))
in (

let uu____23860 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in ((uu____23818), (FStar_Pervasives_Native.Some ("inversion axiom")), (uu____23860))))
in (FStar_SMTEncoding_Util.mkAssume uu____23811)))
in (FStar_List.append decls ((fuel_guarded_inversion)::[])))
end))
end))
end))
end)))
in (

let uu____23863 = (

let uu____23876 = (

let uu____23877 = (FStar_Syntax_Subst.compress k)
in uu____23877.FStar_Syntax_Syntax.n)
in (match (uu____23876) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____23922 -> begin
((tps), (k))
end))
in (match (uu____23863) with
| (formals, res) -> begin
(

let uu____23945 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____23945) with
| (formals1, res1) -> begin
(

let uu____23956 = (encode_binders FStar_Pervasives_Native.None formals1 env)
in (match (uu____23956) with
| (vars, guards, env', binder_decls, uu____23981) -> begin
(

let uu____23994 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____23994) with
| (tname, ttok, env1) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____24013 = (

let uu____24020 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____24020)))
in (FStar_SMTEncoding_Util.mkApp uu____24013))
in (

let uu____24029 = (

let tname_decl = (

let uu____24039 = (

let uu____24040 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____24072 -> (match (uu____24072) with
| (n1, s) -> begin
(((Prims.strcat tname n1)), (s), (false))
end))))
in (

let uu____24085 = (varops.next_id ())
in ((tname), (uu____24040), (FStar_SMTEncoding_Term.Term_sort), (uu____24085), (false))))
in (constructor_or_logic_type_decl uu____24039))
in (

let uu____24094 = (match (vars) with
| [] -> begin
(

let uu____24107 = (

let uu____24108 = (

let uu____24111 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_45 -> FStar_Pervasives_Native.Some (_0_45)) uu____24111))
in (push_free_var env1 t tname uu____24108))
in (([]), (uu____24107)))
end
| uu____24118 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("token"))))
in (

let ttok_fresh = (

let uu____24127 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____24127))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____24141 = (

let uu____24148 = (

let uu____24149 = (

let uu____24164 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (FStar_Pervasives_Native.None), (vars), (uu____24164)))
in (FStar_SMTEncoding_Util.mkForall' uu____24149))
in ((uu____24148), (FStar_Pervasives_Native.Some ("name-token correspondence")), ((Prims.strcat "token_correspondence_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____24141))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env1)))))))
end)
in (match (uu____24094) with
| (tok_decls, env2) -> begin
(((FStar_List.append tname_decl tok_decls)), (env2))
end)))
in (match (uu____24029) with
| (decls, env2) -> begin
(

let kindingAx = (

let uu____24204 = (encode_term_pred FStar_Pervasives_Native.None res1 env' tapp)
in (match (uu____24204) with
| (k1, decls1) -> begin
(

let karr = (match (((FStar_List.length formals1) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____24222 = (

let uu____24223 = (

let uu____24230 = (

let uu____24231 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____24231))
in ((uu____24230), (FStar_Pervasives_Native.Some ("kinding")), ((Prims.strcat "pre_kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____24223))
in (uu____24222)::[])
end
| uu____24234 -> begin
[]
end)
in (

let uu____24235 = (

let uu____24238 = (

let uu____24241 = (

let uu____24242 = (

let uu____24249 = (

let uu____24250 = (

let uu____24261 = (FStar_SMTEncoding_Util.mkImp ((guard), (k1)))
in ((((tapp)::[])::[]), (vars), (uu____24261)))
in (FStar_SMTEncoding_Util.mkForall uu____24250))
in ((uu____24249), (FStar_Pervasives_Native.None), ((Prims.strcat "kinding_" ttok))))
in (FStar_SMTEncoding_Util.mkAssume uu____24242))
in (uu____24241)::[])
in (FStar_List.append karr uu____24238))
in (FStar_List.append decls1 uu____24235)))
end))
in (

let aux = (

let uu____24277 = (

let uu____24280 = (inversion_axioms tapp vars)
in (

let uu____24283 = (

let uu____24286 = (pretype_axiom env2 tapp vars)
in (uu____24286)::[])
in (FStar_List.append uu____24280 uu____24283)))
in (FStar_List.append kindingAx uu____24277))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env2)))))
end)))))
end))
end))
end))
end))))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____24293, uu____24294, uu____24295, uu____24296, uu____24297) when (FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____24305, t, uu____24307, n_tps, uu____24309) -> begin
(

let quals = se.FStar_Syntax_Syntax.sigquals
in (

let uu____24317 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____24317) with
| (ddconstrsym, ddtok, env1) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____24334 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____24334) with
| (formals, t_res) -> begin
(

let uu____24369 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____24369) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____24383 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____24383) with
| (vars, guards, env', binder_decls, names1) -> begin
(

let fields = (FStar_All.pipe_right names1 (FStar_List.mapi (fun n1 x -> (

let projectible = true
in (

let uu____24453 = (mk_term_projector_name d x)
in ((uu____24453), (FStar_SMTEncoding_Term.Term_sort), (projectible)))))))
in (

let datacons = (

let uu____24455 = (

let uu____24474 = (varops.next_id ())
in ((ddconstrsym), (fields), (FStar_SMTEncoding_Term.Term_sort), (uu____24474), (true)))
in (FStar_All.pipe_right uu____24455 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____24513 = (encode_term_pred FStar_Pervasives_Native.None t env1 ddtok_tm)
in (match (uu____24513) with
| (tok_typing, decls3) -> begin
(

let tok_typing1 = (match (fields) with
| (uu____24525)::uu____24526 -> begin
(

let ff = (("ty"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV ff)
in (

let vtok_app_l = (mk_Apply ddtok_tm ((ff)::[]))
in (

let vtok_app_r = (mk_Apply f ((((ddtok), (FStar_SMTEncoding_Term.Term_sort)))::[]))
in (

let uu____24571 = (

let uu____24582 = (FStar_SMTEncoding_Term.mk_NoHoist f tok_typing)
in ((((vtok_app_l)::[])::((vtok_app_r)::[])::[]), ((ff)::[]), (uu____24582)))
in (FStar_SMTEncoding_Util.mkForall uu____24571))))))
end
| uu____24607 -> begin
tok_typing
end)
in (

let uu____24616 = (encode_binders (FStar_Pervasives_Native.Some (fuel_tm)) formals env1)
in (match (uu____24616) with
| (vars', guards', env'', decls_formals, uu____24641) -> begin
(

let uu____24654 = (

let xvars1 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp1 = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars1)))
in (encode_term_pred (FStar_Pervasives_Native.Some (fuel_tm)) t_res env'' dapp1)))
in (match (uu____24654) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____24685 -> begin
(

let uu____24692 = (

let uu____24693 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____24693))
in (uu____24692)::[])
end)
in (

let encode_elim = (fun uu____24703 -> (

let uu____24704 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____24704) with
| (head1, args) -> begin
(

let uu____24747 = (

let uu____24748 = (FStar_Syntax_Subst.compress head1)
in uu____24748.FStar_Syntax_Syntax.n)
in (match (uu____24747) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____24758; FStar_Syntax_Syntax.vars = uu____24759}, uu____24760) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____24766 = (encode_args args env')
in (match (uu____24766) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____24809 -> begin
(

let uu____24810 = (

let uu____24811 = (

let uu____24816 = (

let uu____24817 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____24817))
in ((uu____24816), (orig_arg.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____24811))
in (FStar_Exn.raise uu____24810))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____24833 = (

let uu____24834 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____24834))
in (match (uu____24833) with
| true -> begin
(

let uu____24847 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____24847)::[])
end
| uu____24848 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____24849 = (

let uu____24862 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____24912 uu____24913 -> (match (((uu____24912), (uu____24913))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____25008 = (

let uu____25015 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____25015))
in (match (uu____25008) with
| (uu____25028, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____25036 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____25036)::eqns_or_guards)
end
| uu____25037 -> begin
(

let uu____25038 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____25038)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____24862))
in (match (uu____24849) with
| (uu____25053, arg_vars, elim_eqns_or_guards, uu____25056) -> begin
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

let uu____25086 = (

let uu____25093 = (

let uu____25094 = (

let uu____25105 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25116 = (

let uu____25117 = (

let uu____25122 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____25122)))
in (FStar_SMTEncoding_Util.mkImp uu____25117))
in ((((ty_pred)::[])::[]), (uu____25105), (uu____25116))))
in (FStar_SMTEncoding_Util.mkForall uu____25094))
in ((uu____25093), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25086))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____25145 = (varops.fresh "x")
in ((uu____25145), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____25147 = (

let uu____25154 = (

let uu____25155 = (

let uu____25166 = (

let uu____25171 = (

let uu____25174 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____25174)::[])
in (uu____25171)::[])
in (

let uu____25179 = (

let uu____25180 = (

let uu____25185 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____25186 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____25185), (uu____25186))))
in (FStar_SMTEncoding_Util.mkImp uu____25180))
in ((uu____25166), ((x)::[]), (uu____25179))))
in (FStar_SMTEncoding_Util.mkForall uu____25155))
in (

let uu____25205 = (varops.mk_unique "lextop")
in ((uu____25154), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____25205))))
in (FStar_SMTEncoding_Util.mkAssume uu____25147))))
end
| uu____25208 -> begin
(

let prec = (

let uu____25212 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____25239 -> begin
(

let uu____25240 = (

let uu____25241 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____25241 dapp1))
in (uu____25240)::[])
end))))
in (FStar_All.pipe_right uu____25212 FStar_List.flatten))
in (

let uu____25248 = (

let uu____25255 = (

let uu____25256 = (

let uu____25267 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25278 = (

let uu____25279 = (

let uu____25284 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____25284)))
in (FStar_SMTEncoding_Util.mkImp uu____25279))
in ((((ty_pred)::[])::[]), (uu____25267), (uu____25278))))
in (FStar_SMTEncoding_Util.mkForall uu____25256))
in ((uu____25255), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25248)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____25305 = (encode_args args env')
in (match (uu____25305) with
| (encoded_args, arg_decls) -> begin
(

let guards_for_parameter = (fun orig_arg arg xv -> (

let fv1 = (match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv1) -> begin
fv1
end
| uu____25348 -> begin
(

let uu____25349 = (

let uu____25350 = (

let uu____25355 = (

let uu____25356 = (FStar_Syntax_Print.term_to_string orig_arg)
in (FStar_Util.format1 "Inductive type parameter %s must be a variable ; You may want to change it to an index." uu____25356))
in ((uu____25355), (orig_arg.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____25350))
in (FStar_Exn.raise uu____25349))
end)
in (

let guards1 = (FStar_All.pipe_right guards (FStar_List.collect (fun g -> (

let uu____25372 = (

let uu____25373 = (FStar_SMTEncoding_Term.free_variables g)
in (FStar_List.contains fv1 uu____25373))
in (match (uu____25372) with
| true -> begin
(

let uu____25386 = (FStar_SMTEncoding_Term.subst g fv1 xv)
in (uu____25386)::[])
end
| uu____25387 -> begin
[]
end)))))
in (FStar_SMTEncoding_Util.mk_and_l guards1))))
in (

let uu____25388 = (

let uu____25401 = (FStar_List.zip args encoded_args)
in (FStar_List.fold_left (fun uu____25451 uu____25452 -> (match (((uu____25451), (uu____25452))) with
| ((env2, arg_vars, eqns_or_guards, i), (orig_arg, arg)) -> begin
(

let uu____25547 = (

let uu____25554 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (gen_term_var env2 uu____25554))
in (match (uu____25547) with
| (uu____25567, xv, env3) -> begin
(

let eqns = (match ((i < n_tps)) with
| true -> begin
(

let uu____25575 = (guards_for_parameter (FStar_Pervasives_Native.fst orig_arg) arg xv)
in (uu____25575)::eqns_or_guards)
end
| uu____25576 -> begin
(

let uu____25577 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____25577)::eqns_or_guards)
end)
in ((env3), ((xv)::arg_vars), (eqns), ((i + (Prims.parse_int "1")))))
end))
end)) ((env'), ([]), ([]), ((Prims.parse_int "0"))) uu____25401))
in (match (uu____25388) with
| (uu____25592, arg_vars, elim_eqns_or_guards, uu____25595) -> begin
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

let uu____25625 = (

let uu____25632 = (

let uu____25633 = (

let uu____25644 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25655 = (

let uu____25656 = (

let uu____25661 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append elim_eqns_or_guards guards))
in ((ty_pred), (uu____25661)))
in (FStar_SMTEncoding_Util.mkImp uu____25656))
in ((((ty_pred)::[])::[]), (uu____25644), (uu____25655))))
in (FStar_SMTEncoding_Util.mkForall uu____25633))
in ((uu____25632), (FStar_Pervasives_Native.Some ("data constructor typing elim")), ((Prims.strcat "data_elim_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25625))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Parser_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____25684 = (varops.fresh "x")
in ((uu____25684), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____25686 = (

let uu____25693 = (

let uu____25694 = (

let uu____25705 = (

let uu____25710 = (

let uu____25713 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in (uu____25713)::[])
in (uu____25710)::[])
in (

let uu____25718 = (

let uu____25719 = (

let uu____25724 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____25725 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp1)
in ((uu____25724), (uu____25725))))
in (FStar_SMTEncoding_Util.mkImp uu____25719))
in ((uu____25705), ((x)::[]), (uu____25718))))
in (FStar_SMTEncoding_Util.mkForall uu____25694))
in (

let uu____25744 = (varops.mk_unique "lextop")
in ((uu____25693), (FStar_Pervasives_Native.Some ("lextop is top")), (uu____25744))))
in (FStar_SMTEncoding_Util.mkAssume uu____25686))))
end
| uu____25747 -> begin
(

let prec = (

let uu____25751 = (FStar_All.pipe_right vars (FStar_List.mapi (fun i v1 -> (match ((i < n_tps)) with
| true -> begin
[]
end
| uu____25778 -> begin
(

let uu____25779 = (

let uu____25780 = (FStar_SMTEncoding_Util.mkFreeV v1)
in (FStar_SMTEncoding_Util.mk_Precedes uu____25780 dapp1))
in (uu____25779)::[])
end))))
in (FStar_All.pipe_right uu____25751 FStar_List.flatten))
in (

let uu____25787 = (

let uu____25794 = (

let uu____25795 = (

let uu____25806 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____25817 = (

let uu____25818 = (

let uu____25823 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____25823)))
in (FStar_SMTEncoding_Util.mkImp uu____25818))
in ((((ty_pred)::[])::[]), (uu____25806), (uu____25817))))
in (FStar_SMTEncoding_Util.mkForall uu____25795))
in ((uu____25794), (FStar_Pervasives_Native.Some ("subterm ordering")), ((Prims.strcat "subterm_ordering_" ddconstrsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____25787)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end)))
end)))
end
| uu____25842 -> begin
((

let uu____25844 = (

let uu____25845 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____25846 = (FStar_Syntax_Print.term_to_string head1)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____25845 uu____25846)))
in (FStar_Errors.warn se.FStar_Syntax_Syntax.sigrng uu____25844));
(([]), ([]));
)
end))
end)))
in (

let uu____25851 = (encode_elim ())
in (match (uu____25851) with
| (decls2, elim) -> begin
(

let g = (

let uu____25871 = (

let uu____25874 = (

let uu____25877 = (

let uu____25880 = (

let uu____25883 = (

let uu____25884 = (

let uu____25895 = (

let uu____25898 = (

let uu____25899 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____25899))
in FStar_Pervasives_Native.Some (uu____25898))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____25895)))
in FStar_SMTEncoding_Term.DeclFun (uu____25884))
in (uu____25883)::[])
in (

let uu____25904 = (

let uu____25907 = (

let uu____25910 = (

let uu____25913 = (

let uu____25916 = (

let uu____25919 = (

let uu____25922 = (

let uu____25923 = (

let uu____25930 = (

let uu____25931 = (

let uu____25942 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____25942)))
in (FStar_SMTEncoding_Util.mkForall uu____25931))
in ((uu____25930), (FStar_Pervasives_Native.Some ("equality for proxy")), ((Prims.strcat "equality_tok_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____25923))
in (

let uu____25955 = (

let uu____25958 = (

let uu____25959 = (

let uu____25966 = (

let uu____25967 = (

let uu____25978 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____25989 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____25978), (uu____25989))))
in (FStar_SMTEncoding_Util.mkForall uu____25967))
in ((uu____25966), (FStar_Pervasives_Native.Some ("data constructor typing intro")), ((Prims.strcat "data_typing_intro_" ddtok))))
in (FStar_SMTEncoding_Util.mkAssume uu____25959))
in (uu____25958)::[])
in (uu____25922)::uu____25955))
in ((FStar_SMTEncoding_Util.mkAssume ((tok_typing1), (FStar_Pervasives_Native.Some ("typing for data constructor proxy")), ((Prims.strcat "typing_tok_" ddtok)))))::uu____25919)
in (FStar_List.append uu____25916 elim))
in (FStar_List.append decls_pred uu____25913))
in (FStar_List.append decls_formals uu____25910))
in (FStar_List.append proxy_fresh uu____25907))
in (FStar_List.append uu____25880 uu____25904)))
in (FStar_List.append decls3 uu____25877))
in (FStar_List.append decls2 uu____25874))
in (FStar_List.append binder_decls uu____25871))
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
and encode_sigelts : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____26035 se -> (match (uu____26035) with
| (g, env1) -> begin
(

let uu____26055 = (encode_sigelt env1 se)
in (match (uu____26055) with
| (g', env2) -> begin
(((FStar_List.append g g')), (env2))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____26114 -> (match (uu____26114) with
| (i, decls, env1) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____26146) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env1))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env1.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____26152 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env1.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____26152) with
| true -> begin
(

let uu____26153 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____26154 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____26155 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____26153 uu____26154 uu____26155))))
end
| uu____26156 -> begin
()
end));
(

let uu____26157 = (encode_term t1 env1)
in (match (uu____26157) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____26173 = (

let uu____26180 = (

let uu____26181 = (

let uu____26182 = (FStar_Util.digest_of_string t_hash)
in (Prims.strcat uu____26182 (Prims.strcat "_" (Prims.string_of_int i))))
in (Prims.strcat "x_" uu____26181))
in (new_term_constant_from_string env1 x uu____26180))
in (match (uu____26173) with
| (xxsym, xx, env') -> begin
(

let t2 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel FStar_Pervasives_Native.None xx t)
in (

let caption = (

let uu____26198 = (FStar_Options.log_queries ())
in (match (uu____26198) with
| true -> begin
(

let uu____26201 = (

let uu____26202 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____26203 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____26204 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____26202 uu____26203 uu____26204))))
in FStar_Pervasives_Native.Some (uu____26201))
end
| uu____26205 -> begin
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
| FStar_TypeChecker_Env.Binding_lid (x, (uu____26220, t)) -> begin
(

let t_norm = (whnf env1 t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (

let uu____26234 = (encode_free_var false env1 fv t t_norm [])
in (match (uu____26234) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| FStar_TypeChecker_Env.Binding_sig_inst (uu____26257, se, uu____26259) -> begin
(

let uu____26264 = (encode_sigelt env1 se)
in (match (uu____26264) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end
| FStar_TypeChecker_Env.Binding_sig (uu____26281, se) -> begin
(

let uu____26287 = (encode_sigelt env1 se)
in (match (uu____26287) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____26304 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____26304) with
| (uu____26327, decls, env1) -> begin
((decls), (env1))
end))))


let encode_labels : 'Auu____26342 'Auu____26343 . ((Prims.string * FStar_SMTEncoding_Term.sort) * 'Auu____26343 * 'Auu____26342) Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_Term.decl Prims.list) = (fun labs -> (

let prefix1 = (FStar_All.pipe_right labs (FStar_List.map (fun uu____26411 -> (match (uu____26411) with
| (l, uu____26423, uu____26424) -> begin
FStar_SMTEncoding_Term.DeclFun ((((FStar_Pervasives_Native.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (FStar_Pervasives_Native.None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____26470 -> (match (uu____26470) with
| (l, uu____26484, uu____26485) -> begin
(

let uu____26494 = (FStar_All.pipe_left (fun _0_46 -> FStar_SMTEncoding_Term.Echo (_0_46)) (FStar_Pervasives_Native.fst l))
in (

let uu____26495 = (

let uu____26498 = (

let uu____26499 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____26499))
in (uu____26498)::[])
in (uu____26494)::uu____26495))
end))))
in ((prefix1), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____26521 = (

let uu____26524 = (

let uu____26525 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____26528 = (

let uu____26529 = (FStar_TypeChecker_Env.current_module tcenv)
in (FStar_All.pipe_right uu____26529 FStar_Ident.string_of_lid))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____26525; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true; current_module_name = uu____26528}))
in (uu____26524)::[])
in (FStar_ST.op_Colon_Equals last_env uu____26521)))


let get_env : FStar_Ident.lident  ->  FStar_TypeChecker_Env.env  ->  env_t = (fun cmn tcenv -> (

let uu____26556 = (FStar_ST.op_Bang last_env)
in (match (uu____26556) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____26578 -> begin
(

let uu___161_26581 = e
in (

let uu____26582 = (FStar_Ident.string_of_lid cmn)
in {bindings = uu___161_26581.bindings; depth = uu___161_26581.depth; tcenv = tcenv; warn = uu___161_26581.warn; cache = uu___161_26581.cache; nolabels = uu___161_26581.nolabels; use_zfuel_name = uu___161_26581.use_zfuel_name; encode_non_total_function_typ = uu___161_26581.encode_non_total_function_typ; current_module_name = uu____26582}))
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____26587 = (FStar_ST.op_Bang last_env)
in (match (uu____26587) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____26608)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env ((env)::tl1))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____26633 -> (

let uu____26634 = (FStar_ST.op_Bang last_env)
in (match (uu____26634) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd1)::tl1 -> begin
(

let refs = (FStar_Util.smap_copy hd1.cache)
in (

let top = (

let uu___162_26663 = hd1
in {bindings = uu___162_26663.bindings; depth = uu___162_26663.depth; tcenv = uu___162_26663.tcenv; warn = uu___162_26663.warn; cache = refs; nolabels = uu___162_26663.nolabels; use_zfuel_name = uu___162_26663.use_zfuel_name; encode_non_total_function_typ = uu___162_26663.encode_non_total_function_typ; current_module_name = uu___162_26663.current_module_name})
in (FStar_ST.op_Colon_Equals last_env ((top)::(hd1)::tl1))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____26685 -> (

let uu____26686 = (FStar_ST.op_Bang last_env)
in (match (uu____26686) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____26707)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env tl1)
end)))


let mark_env : Prims.unit  ->  Prims.unit = (fun uu____26732 -> (push_env ()))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun uu____26736 -> (pop_env ()))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun uu____26740 -> (

let uu____26741 = (FStar_ST.op_Bang last_env)
in (match (uu____26741) with
| (hd1)::(uu____26763)::tl1 -> begin
(FStar_ST.op_Colon_Equals last_env ((hd1)::tl1))
end
| uu____26785 -> begin
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
| ((uu____26850)::uu____26851, FStar_SMTEncoding_Term.Assume (a)) -> begin
FStar_SMTEncoding_Term.Assume ((

let uu___163_26859 = a
in {FStar_SMTEncoding_Term.assumption_term = uu___163_26859.FStar_SMTEncoding_Term.assumption_term; FStar_SMTEncoding_Term.assumption_caption = uu___163_26859.FStar_SMTEncoding_Term.assumption_caption; FStar_SMTEncoding_Term.assumption_name = uu___163_26859.FStar_SMTEncoding_Term.assumption_name; FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids}))
end
| uu____26860 -> begin
d
end))


let fact_dbs_for_lid : env_t  ->  FStar_Ident.lid  ->  FStar_SMTEncoding_Term.fact_db_id Prims.list = (fun env lid -> (

let uu____26877 = (

let uu____26880 = (

let uu____26881 = (FStar_Ident.lid_of_ids lid.FStar_Ident.ns)
in FStar_SMTEncoding_Term.Namespace (uu____26881))
in (

let uu____26882 = (open_fact_db_tags env)
in (uu____26880)::uu____26882))
in (FStar_SMTEncoding_Term.Name (lid))::uu____26877))


let encode_top_level_facts : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env se -> (

let fact_db_ids = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.collect (fact_dbs_for_lid env)))
in (

let uu____26906 = (encode_sigelt env se)
in (match (uu____26906) with
| (g, env1) -> begin
(

let g1 = (FStar_All.pipe_right g (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)))
in ((g1), (env1)))
end))))


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> (

let uu____26944 = (FStar_Options.log_queries ())
in (match (uu____26944) with
| true -> begin
(

let uu____26947 = (

let uu____26948 = (

let uu____26949 = (

let uu____26950 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____26950 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____26949))
in FStar_SMTEncoding_Term.Caption (uu____26948))
in (uu____26947)::decls)
end
| uu____26959 -> begin
decls
end)))
in (

let env = (

let uu____26961 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____26961 tcenv))
in (

let uu____26962 = (encode_top_level_facts env se)
in (match (uu____26962) with
| (decls, env1) -> begin
((set_env env1);
(

let uu____26976 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____26976));
)
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____26988 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____26990 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____26990) with
| true -> begin
(

let uu____26991 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) Prims.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____26991))
end
| uu____26992 -> begin
()
end));
(

let env = (get_env modul.FStar_Syntax_Syntax.name tcenv)
in (

let encode_signature = (fun env1 ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____27026 se -> (match (uu____27026) with
| (g, env2) -> begin
(

let uu____27046 = (encode_top_level_facts env2 se)
in (match (uu____27046) with
| (g', env3) -> begin
(((FStar_List.append g g')), (env3))
end))
end)) (([]), (env1)))))
in (

let uu____27069 = (encode_signature (

let uu___164_27078 = env
in {bindings = uu___164_27078.bindings; depth = uu___164_27078.depth; tcenv = uu___164_27078.tcenv; warn = false; cache = uu___164_27078.cache; nolabels = uu___164_27078.nolabels; use_zfuel_name = uu___164_27078.use_zfuel_name; encode_non_total_function_typ = uu___164_27078.encode_non_total_function_typ; current_module_name = uu___164_27078.current_module_name}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____27069) with
| (decls, env1) -> begin
(

let caption = (fun decls1 -> (

let uu____27095 = (FStar_Options.log_queries ())
in (match (uu____27095) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls1) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____27099 -> begin
decls1
end)))
in ((set_env (

let uu___165_27103 = env1
in {bindings = uu___165_27103.bindings; depth = uu___165_27103.depth; tcenv = uu___165_27103.tcenv; warn = true; cache = uu___165_27103.cache; nolabels = uu___165_27103.nolabels; use_zfuel_name = uu___165_27103.use_zfuel_name; encode_non_total_function_typ = uu___165_27103.encode_non_total_function_typ; current_module_name = uu___165_27103.current_module_name}));
(

let uu____27105 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____27105) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____27106 -> begin
()
end));
(

let decls1 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls1));
))
end))));
)))


let encode_query : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____27160 = (

let uu____27161 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____27161.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____27160));
(

let env = (

let uu____27163 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____27163 tcenv))
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____27175 = (

let rec aux = (fun bindings1 -> (match (bindings1) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____27210 = (aux rest)
in (match (uu____27210) with
| (out, rest1) -> begin
(

let t = (

let uu____27240 = (FStar_Syntax_Util.destruct_typ_as_formula x.FStar_Syntax_Syntax.sort)
in (match (uu____27240) with
| FStar_Pervasives_Native.Some (uu____27245) -> begin
(

let uu____27246 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.t_unit)
in (FStar_Syntax_Util.refine uu____27246 x.FStar_Syntax_Syntax.sort))
end
| uu____27247 -> begin
x.FStar_Syntax_Syntax.sort
end))
in (

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.Primops)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
in (

let uu____27251 = (

let uu____27254 = (FStar_Syntax_Syntax.mk_binder (

let uu___166_27257 = x
in {FStar_Syntax_Syntax.ppname = uu___166_27257.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___166_27257.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1}))
in (uu____27254)::out)
in ((uu____27251), (rest1)))))
end))
end
| uu____27262 -> begin
(([]), (bindings1))
end))
in (

let uu____27269 = (aux bindings)
in (match (uu____27269) with
| (closing, bindings1) -> begin
(

let uu____27294 = (FStar_Syntax_Util.close_forall_no_univs (FStar_List.rev closing) q)
in ((uu____27294), (bindings1)))
end)))
in (match (uu____27175) with
| (q1, bindings1) -> begin
(

let uu____27317 = (

let uu____27322 = (FStar_List.filter (fun uu___131_27327 -> (match (uu___131_27327) with
| FStar_TypeChecker_Env.Binding_sig (uu____27328) -> begin
false
end
| uu____27335 -> begin
true
end)) bindings1)
in (encode_env_bindings env uu____27322))
in (match (uu____27317) with
| (env_decls, env1) -> begin
((

let uu____27353 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____27353) with
| true -> begin
(

let uu____27354 = (FStar_Syntax_Print.term_to_string q1)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____27354))
end
| uu____27355 -> begin
()
end));
(

let uu____27356 = (encode_formula q1 env1)
in (match (uu____27356) with
| (phi, qdecls) -> begin
(

let uu____27377 = (

let uu____27382 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____27382 phi))
in (match (uu____27377) with
| (labels, phi1) -> begin
(

let uu____27399 = (encode_labels labels)
in (match (uu____27399) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____27436 = (

let uu____27443 = (FStar_SMTEncoding_Util.mkNot phi1)
in (

let uu____27444 = (varops.mk_unique "@query")
in ((uu____27443), (FStar_Pervasives_Native.Some ("query")), (uu____27444))))
in (FStar_SMTEncoding_Util.mkAssume uu____27436))
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

let uu____27463 = (FStar_TypeChecker_Env.current_module tcenv)
in (get_env uu____27463 tcenv))
in ((FStar_SMTEncoding_Z3.push "query");
(

let uu____27465 = (encode_formula q env)
in (match (uu____27465) with
| (f, uu____27471) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____27473) -> begin
true
end
| uu____27478 -> begin
false
end);
)
end));
)))





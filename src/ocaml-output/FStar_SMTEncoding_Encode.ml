
open Prims

let add_fuel = (fun x tl -> (

let uu____16 = (FStar_Options.unthrottle_inductives ())
in (match (uu____16) with
| true -> begin
tl
end
| uu____18 -> begin
(x)::tl
end)))


let withenv = (fun c uu____39 -> (match (uu____39) with
| (a, b) -> begin
((a), (b), (c))
end))


let vargs = (fun args -> (FStar_List.filter (fun uu___108_74 -> (match (uu___108_74) with
| (FStar_Util.Inl (uu____79), uu____80) -> begin
false
end
| uu____83 -> begin
true
end)) args))


let subst_lcomp_opt = (fun s l -> (match (l) with
| Some (FStar_Util.Inl (l)) -> begin
(

let uu____114 = (

let uu____117 = (

let uu____118 = (

let uu____121 = (l.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp s uu____121))
in (FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____118))
in FStar_Util.Inl (uu____117))
in Some (uu____114))
end
| uu____126 -> begin
l
end))


let escape : Prims.string  ->  Prims.string = (fun s -> (FStar_Util.replace_char s '\'' '_'))


let mk_term_projector_name : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  Prims.string = (fun lid a -> (

let a = (

let uu___133_140 = a
in (

let uu____141 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____141; FStar_Syntax_Syntax.index = uu___133_140.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___133_140.FStar_Syntax_Syntax.sort}))
in (

let uu____142 = (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str a.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in (FStar_All.pipe_left escape uu____142))))


let primitive_projector_by_pos : FStar_TypeChecker_Env.env  ->  FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun env lid i -> (

let fail = (fun uu____155 -> (

let uu____156 = (

let uu____157 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "Projector %s on data constructor %s not found" uu____157 lid.FStar_Ident.str))
in (failwith uu____156)))
in (

let uu____158 = (FStar_TypeChecker_Env.lookup_datacon env lid)
in (match (uu____158) with
| (uu____161, t) -> begin
(

let uu____163 = (

let uu____164 = (FStar_Syntax_Subst.compress t)
in uu____164.FStar_Syntax_Syntax.n)
in (match (uu____163) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(

let uu____179 = (FStar_Syntax_Subst.open_comp bs c)
in (match (uu____179) with
| (binders, uu____183) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____188 -> begin
(

let b = (FStar_List.nth binders i)
in (mk_term_projector_name lid (Prims.fst b)))
end)
end))
end
| uu____194 -> begin
(fail ())
end))
end))))


let mk_term_projector_name_by_pos : FStar_Ident.lident  ->  Prims.int  ->  Prims.string = (fun lid i -> (

let uu____201 = (

let uu____202 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "%s_%s" lid.FStar_Ident.str uu____202))
in (FStar_All.pipe_left escape uu____201)))


let mk_term_projector : FStar_Ident.lident  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun lid a -> (

let uu____209 = (

let uu____212 = (mk_term_projector_name lid a)
in ((uu____212), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____209)))


let mk_term_projector_by_pos : FStar_Ident.lident  ->  Prims.int  ->  FStar_SMTEncoding_Term.term = (fun lid i -> (

let uu____219 = (

let uu____222 = (mk_term_projector_name_by_pos lid i)
in ((uu____222), (FStar_SMTEncoding_Term.Arrow (((FStar_SMTEncoding_Term.Term_sort), (FStar_SMTEncoding_Term.Term_sort))))))
in (FStar_SMTEncoding_Util.mkFreeV uu____219)))


let mk_data_tester = (fun env l x -> (FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x))

type varops_t =
{push : Prims.unit  ->  Prims.unit; pop : Prims.unit  ->  Prims.unit; mark : Prims.unit  ->  Prims.unit; reset_mark : Prims.unit  ->  Prims.unit; commit_mark : Prims.unit  ->  Prims.unit; new_var : FStar_Ident.ident  ->  Prims.int  ->  Prims.string; new_fvar : FStar_Ident.lident  ->  Prims.string; fresh : Prims.string  ->  Prims.string; string_const : Prims.string  ->  FStar_SMTEncoding_Term.term; next_id : Prims.unit  ->  Prims.int; mk_unique : Prims.string  ->  Prims.string}


let varops : varops_t = (

let initial_ctr = (Prims.parse_int "100")
in (

let ctr = (FStar_Util.mk_ref initial_ctr)
in (

let new_scope = (fun uu____412 -> (

let uu____413 = (FStar_Util.smap_create (Prims.parse_int "100"))
in (

let uu____415 = (FStar_Util.smap_create (Prims.parse_int "100"))
in ((uu____413), (uu____415)))))
in (

let scopes = (

let uu____426 = (

let uu____432 = (new_scope ())
in (uu____432)::[])
in (FStar_Util.mk_ref uu____426))
in (

let mk_unique = (fun y -> (

let y = (escape y)
in (

let y = (

let uu____457 = (

let uu____459 = (FStar_ST.read scopes)
in (FStar_Util.find_map uu____459 (fun uu____476 -> (match (uu____476) with
| (names, uu____483) -> begin
(FStar_Util.smap_try_find names y)
end))))
in (match (uu____457) with
| None -> begin
y
end
| Some (uu____488) -> begin
((FStar_Util.incr ctr);
(

let uu____493 = (

let uu____494 = (

let uu____495 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int uu____495))
in (Prims.strcat "__" uu____494))
in (Prims.strcat y uu____493));
)
end))
in (

let top_scope = (

let uu____500 = (

let uu____505 = (FStar_ST.read scopes)
in (FStar_List.hd uu____505))
in (FStar_All.pipe_left Prims.fst uu____500))
in ((FStar_Util.smap_add top_scope y true);
y;
)))))
in (

let new_var = (fun pp rn -> (

let uu____537 = (

let uu____538 = (

let uu____539 = (FStar_Util.string_of_int rn)
in (Prims.strcat "__" uu____539))
in (Prims.strcat pp.FStar_Ident.idText uu____538))
in (FStar_All.pipe_left mk_unique uu____537)))
in (

let new_fvar = (fun lid -> (mk_unique lid.FStar_Ident.str))
in (

let next_id = (fun uu____547 -> ((FStar_Util.incr ctr);
(FStar_ST.read ctr);
))
in (

let fresh = (fun pfx -> (

let uu____558 = (

let uu____559 = (next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____559))
in (FStar_Util.format2 "%s_%s" pfx uu____558)))
in (

let string_const = (fun s -> (

let uu____564 = (

let uu____566 = (FStar_ST.read scopes)
in (FStar_Util.find_map uu____566 (fun uu____583 -> (match (uu____583) with
| (uu____589, strings) -> begin
(FStar_Util.smap_try_find strings s)
end))))
in (match (uu____564) with
| Some (f) -> begin
f
end
| None -> begin
(

let id = (next_id ())
in (

let f = (

let uu____598 = (FStar_SMTEncoding_Util.mk_String_const id)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____598))
in (

let top_scope = (

let uu____601 = (

let uu____606 = (FStar_ST.read scopes)
in (FStar_List.hd uu____606))
in (FStar_All.pipe_left Prims.snd uu____601))
in ((FStar_Util.smap_add top_scope s f);
f;
))))
end)))
in (

let push = (fun uu____634 -> (

let uu____635 = (

let uu____641 = (new_scope ())
in (

let uu____646 = (FStar_ST.read scopes)
in (uu____641)::uu____646))
in (FStar_ST.write scopes uu____635)))
in (

let pop = (fun uu____673 -> (

let uu____674 = (

let uu____680 = (FStar_ST.read scopes)
in (FStar_List.tl uu____680))
in (FStar_ST.write scopes uu____674)))
in (

let mark = (fun uu____707 -> (push ()))
in (

let reset_mark = (fun uu____711 -> (pop ()))
in (

let commit_mark = (fun uu____715 -> (

let uu____716 = (FStar_ST.read scopes)
in (match (uu____716) with
| ((hd1, hd2))::((next1, next2))::tl -> begin
((FStar_Util.smap_fold hd1 (fun key value v -> (FStar_Util.smap_add next1 key value)) ());
(FStar_Util.smap_fold hd2 (fun key value v -> (FStar_Util.smap_add next2 key value)) ());
(FStar_ST.write scopes ((((next1), (next2)))::tl));
)
end
| uu____776 -> begin
(failwith "Impossible")
end)))
in {push = push; pop = pop; mark = mark; reset_mark = reset_mark; commit_mark = commit_mark; new_var = new_var; new_fvar = new_fvar; fresh = fresh; string_const = string_const; next_id = next_id; mk_unique = mk_unique})))))))))))))))


let unmangle : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv = (fun x -> (

let uu___134_785 = x
in (

let uu____786 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____786; FStar_Syntax_Syntax.index = uu___134_785.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___134_785.FStar_Syntax_Syntax.sort})))

type binding =
| Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
| Binding_fvar of (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option)


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____807 -> begin
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
| uu____831 -> begin
false
end))


let __proj__Binding_fvar__item___0 : binding  ->  (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun projectee -> (match (projectee) with
| Binding_fvar (_0) -> begin
_0
end))


let binder_of_eithervar = (fun v -> ((v), (None)))

type env_t =
{bindings : binding Prims.list; depth : Prims.int; tcenv : FStar_TypeChecker_Env.env; warn : Prims.bool; cache : (Prims.string * FStar_SMTEncoding_Term.sort Prims.list * FStar_SMTEncoding_Term.decl Prims.list) FStar_Util.smap; nolabels : Prims.bool; use_zfuel_name : Prims.bool; encode_non_total_function_typ : Prims.bool}


let print_env : env_t  ->  Prims.string = (fun e -> (

let uu____950 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun uu___109_954 -> (match (uu___109_954) with
| Binding_var (x, uu____956) -> begin
(FStar_Syntax_Print.bv_to_string x)
end
| Binding_fvar (l, uu____958, uu____959, uu____960) -> begin
(FStar_Syntax_Print.lid_to_string l)
end))))
in (FStar_All.pipe_right uu____950 (FStar_String.concat ", "))))


let lookup_binding = (fun env f -> (FStar_Util.find_map env.bindings f))


let caption_t : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.string Prims.option = (fun env t -> (

let uu____993 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____993) with
| true -> begin
(

let uu____995 = (FStar_Syntax_Print.term_to_string t)
in Some (uu____995))
end
| uu____996 -> begin
None
end)))


let fresh_fvar : Prims.string  ->  FStar_SMTEncoding_Term.sort  ->  (Prims.string * FStar_SMTEncoding_Term.term) = (fun x s -> (

let xsym = (varops.fresh x)
in (

let uu____1006 = (FStar_SMTEncoding_Util.mkFreeV ((xsym), (s)))
in ((xsym), (uu____1006)))))


let gen_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (

let uu____1017 = (FStar_Util.string_of_int env.depth)
in (Prims.strcat "@x" uu____1017))
in (

let y = (FStar_SMTEncoding_Util.mkFreeV ((ysym), (FStar_SMTEncoding_Term.Term_sort)))
in ((ysym), (y), ((

let uu___135_1019 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___135_1019.tcenv; warn = uu___135_1019.warn; cache = uu___135_1019.cache; nolabels = uu___135_1019.nolabels; use_zfuel_name = uu___135_1019.use_zfuel_name; encode_non_total_function_typ = uu___135_1019.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___136_1032 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___136_1032.depth; tcenv = uu___136_1032.tcenv; warn = uu___136_1032.warn; cache = uu___136_1032.cache; nolabels = uu___136_1032.nolabels; use_zfuel_name = uu___136_1032.use_zfuel_name; encode_non_total_function_typ = uu___136_1032.encode_non_total_function_typ}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___137_1048 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___137_1048.depth; tcenv = uu___137_1048.tcenv; warn = uu___137_1048.warn; cache = uu___137_1048.cache; nolabels = uu___137_1048.nolabels; use_zfuel_name = uu___137_1048.use_zfuel_name; encode_non_total_function_typ = uu___137_1048.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___138_1058 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = uu___138_1058.depth; tcenv = uu___138_1058.tcenv; warn = uu___138_1058.warn; cache = uu___138_1058.cache; nolabels = uu___138_1058.nolabels; use_zfuel_name = uu___138_1058.use_zfuel_name; encode_non_total_function_typ = uu___138_1058.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun uu___110_1074 -> (match (uu___110_1074) with
| Binding_var (b, t) when (FStar_Syntax_Syntax.bv_eq b a') -> begin
Some (((b), (t)))
end
| uu____1082 -> begin
None
end))))
in (

let uu____1085 = (aux a)
in (match (uu____1085) with
| None -> begin
(

let a = (unmangle a)
in (

let uu____1092 = (aux a)
in (match (uu____1092) with
| None -> begin
(

let uu____1098 = (

let uu____1099 = (FStar_Syntax_Print.bv_to_string a)
in (FStar_Util.format1 "Bound term variable not found (after unmangling): %s" uu____1099))
in (failwith uu____1098))
end
| Some (b, t) -> begin
t
end)))
end
| Some (b, t) -> begin
t
end))))


let new_term_constant_and_tok_from_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * Prims.string * env_t) = (fun env x -> (

let fname = (varops.new_fvar x)
in (

let ftok = (Prims.strcat fname "@tok")
in (

let uu____1119 = (

let uu___139_1120 = env
in (

let uu____1121 = (

let uu____1123 = (

let uu____1124 = (

let uu____1131 = (

let uu____1133 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _0_29 -> Some (_0_29)) uu____1133))
in ((x), (fname), (uu____1131), (None)))
in Binding_fvar (uu____1124))
in (uu____1123)::env.bindings)
in {bindings = uu____1121; depth = uu___139_1120.depth; tcenv = uu___139_1120.tcenv; warn = uu___139_1120.warn; cache = uu___139_1120.cache; nolabels = uu___139_1120.nolabels; use_zfuel_name = uu___139_1120.use_zfuel_name; encode_non_total_function_typ = uu___139_1120.encode_non_total_function_typ}))
in ((fname), (ftok), (uu____1119))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun uu___111_1155 -> (match (uu___111_1155) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| uu____1177 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (

let uu____1189 = (lookup_binding env (fun uu___112_1191 -> (match (uu___112_1191) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| uu____1201 -> begin
None
end)))
in (FStar_All.pipe_right uu____1189 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (

let uu____1214 = (try_lookup_lid env a)
in (match (uu____1214) with
| None -> begin
(

let uu____1231 = (

let uu____1232 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____1232))
in (failwith uu____1231))
end
| Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let uu___140_1263 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = uu___140_1263.depth; tcenv = uu___140_1263.tcenv; warn = uu___140_1263.warn; cache = uu___140_1263.cache; nolabels = uu___140_1263.nolabels; use_zfuel_name = uu___140_1263.use_zfuel_name; encode_non_total_function_typ = uu___140_1263.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let uu____1275 = (lookup_lid env x)
in (match (uu____1275) with
| (t1, t2, uu____1283) -> begin
(

let t3 = (

let uu____1289 = (

let uu____1293 = (

let uu____1295 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____1295)::[])
in ((f), (uu____1293)))
in (FStar_SMTEncoding_Util.mkApp uu____1289))
in (

let uu___141_1298 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = uu___141_1298.depth; tcenv = uu___141_1298.tcenv; warn = uu___141_1298.warn; cache = uu___141_1298.cache; nolabels = uu___141_1298.nolabels; use_zfuel_name = uu___141_1298.use_zfuel_name; encode_non_total_function_typ = uu___141_1298.encode_non_total_function_typ}))
end)))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env l -> (

let uu____1308 = (try_lookup_lid env l)
in (match (uu____1308) with
| None -> begin
None
end
| Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
Some (f)
end
| uu____1335 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____1340, (fuel)::[]) -> begin
(

let uu____1343 = (

let uu____1344 = (

let uu____1345 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____1345 Prims.fst))
in (FStar_Util.starts_with uu____1344 "fuel"))
in (match (uu____1343) with
| true -> begin
(

let uu____1347 = (

let uu____1348 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____1348 fuel))
in (FStar_All.pipe_left (fun _0_30 -> Some (_0_30)) uu____1347))
end
| uu____1350 -> begin
Some (t)
end))
end
| uu____1351 -> begin
Some (t)
end)
end
| uu____1352 -> begin
None
end)
end)
end)))


let lookup_free_var = (fun env a -> (

let uu____1370 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____1370) with
| Some (t) -> begin
t
end
| None -> begin
(

let uu____1373 = (

let uu____1374 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____1374))
in (failwith uu____1373))
end)))


let lookup_free_var_name = (fun env a -> (

let uu____1391 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____1391) with
| (x, uu____1398, uu____1399) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let uu____1423 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____1423) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____1444; FStar_SMTEncoding_Term.rng = uu____1445}) when env.use_zfuel_name -> begin
((g), (zf))
end
| uu____1453 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| uu____1467 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___113_1476 -> (match (uu___113_1476) with
| Binding_fvar (uu____1478, nm', tok, uu____1481) when (nm = nm') -> begin
tok
end
| uu____1486 -> begin
None
end))))


let mkForall_fuel' = (fun n uu____1503 -> (match (uu____1503) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____1519 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____1522 = (FStar_Options.unthrottle_inductives ())
in (match (uu____1522) with
| true -> begin
(fallback ())
end
| uu____1523 -> begin
(

let uu____1524 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____1524) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____1543 -> begin
p
end)))))
in (

let pats = (FStar_List.map add_fuel pats)
in (

let body = (match (body.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (guard)::(body')::[]) -> begin
(

let guard = (match (guard.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, guards) -> begin
(

let uu____1557 = (add_fuel guards)
in (FStar_SMTEncoding_Util.mk_and_l uu____1557))
end
| uu____1559 -> begin
(

let uu____1560 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right uu____1560 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard), (body'))))
end
| uu____1563 -> begin
body
end)
in (

let vars = (((fsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars
in (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body)))))))
end))
end)))
end))


let mkForall_fuel : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' (Prims.parse_int "1"))


let head_normal : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t = (FStar_Syntax_Util.unmeta t)
in (match (t.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_refine (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) -> begin
true
end
| (FStar_Syntax_Syntax.Tm_fvar (fv)) | (FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) -> begin
(

let uu____1607 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____1607 FStar_Option.isNone))
end
| uu____1620 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____1627 = (

let uu____1628 = (FStar_Syntax_Util.un_uinst t)
in uu____1628.FStar_Syntax_Syntax.n)
in (match (uu____1627) with
| FStar_Syntax_Syntax.Tm_abs (uu____1631, uu____1632, Some (FStar_Util.Inr (l, flags))) -> begin
(((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___114_1661 -> (match (uu___114_1661) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____1662 -> begin
false
end)) flags))
end
| FStar_Syntax_Syntax.Tm_abs (uu____1663, uu____1664, Some (FStar_Util.Inl (lc))) -> begin
(FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____1691 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____1691 FStar_Option.isSome))
end
| uu____1704 -> begin
false
end)))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1711 = (head_normal env t)
in (match (uu____1711) with
| true -> begin
t
end
| uu____1712 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____1722 = (

let uu____1726 = (FStar_Syntax_Syntax.null_binder t)
in (uu____1726)::[])
in (

let uu____1727 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs uu____1722 uu____1727 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(

let uu____1754 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out uu____1754))
end
| s -> begin
(

let uu____1757 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out uu____1757))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___115_1769 -> (match (uu___115_1769) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| uu____1770 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____1798; FStar_SMTEncoding_Term.rng = uu____1799})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____1813) -> begin
(

let uu____1818 = (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| uu____1828 -> begin
false
end)) args vars))
in (match (uu____1818) with
| true -> begin
(tok_of_name env f)
end
| uu____1830 -> begin
None
end))
end
| (uu____1831, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____1834 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (

let uu____1836 = (FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)
in (not (uu____1836))))))
in (match (uu____1834) with
| true -> begin
Some (t)
end
| uu____1838 -> begin
None
end)))
end
| uu____1839 -> begin
None
end))
in (aux t (FStar_List.rev vars))))


type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)


type labels =
label Prims.list

type pattern =
{pat_vars : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list; pat_term : Prims.unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t); guard : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term; projections : FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list}

exception Let_rec_unencodeable


let uu___is_Let_rec_unencodeable : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Let_rec_unencodeable -> begin
true
end
| uu____1923 -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun uu___116_1926 -> (match (uu___116_1926) with
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

let uu____1928 = (

let uu____1932 = (

let uu____1934 = (

let uu____1935 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt uu____1935))
in (uu____1934)::[])
in (("FStar.Char.Char"), (uu____1932)))
in (FStar_SMTEncoding_Util.mkApp uu____1928))
end
| FStar_Const.Const_int (i, None) -> begin
(

let uu____1943 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____1943))
end
| FStar_Const.Const_int (i, Some (uu____1945)) -> begin
(failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, uu____1954) -> begin
(

let uu____1957 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const uu____1957))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(

let uu____1961 = (

let uu____1962 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" uu____1962))
in (failwith uu____1961))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1981) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (uu____1989) -> begin
(

let uu____1994 = (FStar_Syntax_Util.unrefine t)
in (aux true uu____1994))
end
| uu____1995 -> begin
(match (norm) with
| true -> begin
(

let uu____1996 = (whnf env t)
in (aux false uu____1996))
end
| uu____1997 -> begin
(

let uu____1998 = (

let uu____1999 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____2000 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____1999 uu____2000)))
in (failwith uu____1998))
end)
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| uu____2021 -> begin
(

let uu____2022 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____2022)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____2165 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____2165) with
| true -> begin
(

let uu____2166 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____2166))
end
| uu____2167 -> begin
()
end));
(

let uu____2168 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2204 b -> (match (uu____2204) with
| (vars, guards, env, decls, names) -> begin
(

let uu____2247 = (

let x = (unmangle (Prims.fst b))
in (

let uu____2256 = (gen_term_var env x)
in (match (uu____2256) with
| (xxsym, xx, env') -> begin
(

let uu____2270 = (

let uu____2273 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____2273 env xx))
in (match (uu____2270) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____2247) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____2168) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2361 = (encode_term t env)
in (match (uu____2361) with
| (t, decls) -> begin
(

let uu____2368 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((uu____2368), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2376 = (encode_term t env)
in (match (uu____2376) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(

let uu____2385 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((uu____2385), (decls)))
end
| Some (f) -> begin
(

let uu____2387 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((uu____2387), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____2394 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____2394) with
| true -> begin
(

let uu____2395 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____2396 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____2397 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____2395 uu____2396 uu____2397))))
end
| uu____2398 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(

let uu____2402 = (

let uu____2403 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____2404 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____2405 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____2406 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2403 uu____2404 uu____2405 uu____2406)))))
in (failwith uu____2402))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____2410 = (

let uu____2411 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____2411))
in (failwith uu____2410))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, uu____2416) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____2436) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(

let uu____2445 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((uu____2445), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____2451) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____2454) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____2460 = (encode_const c)
in ((uu____2460), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____2474 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____2474) with
| (binders, res) -> begin
(

let uu____2481 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____2481) with
| true -> begin
(

let uu____2484 = (encode_binders None binders env)
in (match (uu____2484) with
| (vars, guards, env', decls, uu____2499) -> begin
(

let fsym = (

let uu____2509 = (varops.fresh "f")
in ((uu____2509), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____2512 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___142_2516 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___142_2516.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___142_2516.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___142_2516.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___142_2516.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___142_2516.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___142_2516.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___142_2516.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___142_2516.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___142_2516.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___142_2516.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___142_2516.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___142_2516.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___142_2516.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___142_2516.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___142_2516.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___142_2516.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___142_2516.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___142_2516.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___142_2516.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___142_2516.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___142_2516.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___142_2516.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___142_2516.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (uu____2512) with
| (pre_opt, res_t) -> begin
(

let uu____2523 = (encode_term_pred None res_t env' app)
in (match (uu____2523) with
| (res_pred, decls') -> begin
(

let uu____2530 = (match (pre_opt) with
| None -> begin
(

let uu____2537 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____2537), ([])))
end
| Some (pre) -> begin
(

let uu____2540 = (encode_formula pre env')
in (match (uu____2540) with
| (guard, decls0) -> begin
(

let uu____2548 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____2548), (decls0)))
end))
end)
in (match (uu____2530) with
| (guards, guard_decls) -> begin
(

let t_interp = (

let uu____2556 = (

let uu____2562 = (FStar_SMTEncoding_Util.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____2562)))
in (FStar_SMTEncoding_Util.mkForall uu____2556))
in (

let cvars = (

let uu____2572 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____2572 (FStar_List.filter (fun uu____2578 -> (match (uu____2578) with
| (x, uu____2582) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____2593 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____2593) with
| Some (t', sorts, uu____2609) -> begin
(

let uu____2619 = (

let uu____2620 = (

let uu____2624 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t'), (uu____2624)))
in (FStar_SMTEncoding_Util.mkApp uu____2620))
in ((uu____2619), ([])))
end
| None -> begin
(

let tsym = (

let uu____2640 = (

let uu____2641 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____2641))
in (varops.mk_unique uu____2640))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = (

let uu____2648 = (FStar_Options.log_queries ())
in (match (uu____2648) with
| true -> begin
(

let uu____2650 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (uu____2650))
end
| uu____2651 -> begin
None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (

let uu____2656 = (

let uu____2660 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____2660)))
in (FStar_SMTEncoding_Util.mkApp uu____2656))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (

let uu____2669 = (

let uu____2674 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____2674), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2669)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (

let uu____2689 = (

let uu____2694 = (

let uu____2695 = (

let uu____2701 = (

let uu____2702 = (

let uu____2705 = (

let uu____2706 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____2706))
in ((f_has_t), (uu____2705)))
in (FStar_SMTEncoding_Util.mkImp uu____2702))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____2701)))
in (mkForall_fuel uu____2695))
in ((uu____2694), (Some ("pre-typing for functions")), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2689)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (

let uu____2721 = (

let uu____2726 = (

let uu____2727 = (

let uu____2733 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____2733)))
in (FStar_SMTEncoding_Util.mkForall uu____2727))
in ((uu____2726), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2721)))
in (

let t_decls = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp)::[]))))
in ((FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)));
((t), (t_decls));
)))))))))))))
end))))))
end))
end))
end)))))
end))
end
| uu____2756 -> begin
(

let tsym = (varops.fresh "Non_total_Tm_arrow")
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (FStar_SMTEncoding_Util.mkApp ((tsym), ([])))
in (

let t_kinding = (

let a_name = Some ((Prims.strcat "non_total_function_typing_" tsym))
in (

let uu____2766 = (

let uu____2771 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____2771), (Some ("Typing for non-total arrows")), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2766)))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let t_interp = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (

let uu____2782 = (

let uu____2787 = (

let uu____2788 = (

let uu____2794 = (

let uu____2795 = (

let uu____2798 = (

let uu____2799 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____2799))
in ((f_has_t), (uu____2798)))
in (FStar_SMTEncoding_Util.mkImp uu____2795))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____2794)))
in (mkForall_fuel uu____2788))
in ((uu____2787), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2782)))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_refine (uu____2814) -> begin
(

let uu____2819 = (

let uu____2822 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____2822) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = uu____2827; FStar_Syntax_Syntax.pos = uu____2828; FStar_Syntax_Syntax.vars = uu____2829} -> begin
(

let uu____2836 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (uu____2836) with
| (b, f) -> begin
(

let uu____2850 = (

let uu____2851 = (FStar_List.hd b)
in (Prims.fst uu____2851))
in ((uu____2850), (f)))
end))
end
| uu____2856 -> begin
(failwith "impossible")
end))
in (match (uu____2819) with
| (x, f) -> begin
(

let uu____2863 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____2863) with
| (base_t, decls) -> begin
(

let uu____2870 = (gen_term_var env x)
in (match (uu____2870) with
| (x, xtm, env') -> begin
(

let uu____2879 = (encode_formula f env')
in (match (uu____2879) with
| (refinement, decls') -> begin
(

let uu____2886 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____2886) with
| (fsym, fterm) -> begin
(

let encoding = (

let uu____2894 = (

let uu____2897 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((uu____2897), (refinement)))
in (FStar_SMTEncoding_Util.mkAnd uu____2894))
in (

let cvars = (

let uu____2902 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right uu____2902 (FStar_List.filter (fun uu____2908 -> (match (uu____2908) with
| (y, uu____2912) -> begin
((y <> x) && (y <> fsym))
end)))))
in (

let xfv = ((x), (FStar_SMTEncoding_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_SMTEncoding_Term.Fuel_sort))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((ffv)::(xfv)::cvars), (encoding)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____2931 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____2931) with
| Some (t, uu____2946, uu____2947) -> begin
(

let uu____2957 = (

let uu____2958 = (

let uu____2962 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t), (uu____2962)))
in (FStar_SMTEncoding_Util.mkApp uu____2958))
in ((uu____2957), ([])))
end
| None -> begin
(

let tsym = (

let uu____2978 = (

let uu____2979 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_refine_" uu____2979))
in (varops.mk_unique uu____2978))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (

let uu____2988 = (

let uu____2992 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____2992)))
in (FStar_SMTEncoding_Util.mkApp uu____2988))
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm t)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t)
in (

let t_haseq = (

let uu____3002 = (

let uu____3007 = (

let uu____3008 = (

let uu____3014 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (uu____3014)))
in (FStar_SMTEncoding_Util.mkForall uu____3008))
in ((uu____3007), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym)))))
in FStar_SMTEncoding_Term.Assume (uu____3002))
in (

let t_kinding = (

let uu____3025 = (

let uu____3030 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____3030), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym)))))
in FStar_SMTEncoding_Term.Assume (uu____3025))
in (

let t_interp = (

let uu____3041 = (

let uu____3046 = (

let uu____3047 = (

let uu____3053 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (uu____3053)))
in (FStar_SMTEncoding_Util.mkForall uu____3047))
in (

let uu____3065 = (

let uu____3067 = (FStar_Syntax_Print.term_to_string t0)
in Some (uu____3067))
in ((uu____3046), (uu____3065), (Some ((Prims.strcat "refinement_interpretation_" tsym))))))
in FStar_SMTEncoding_Term.Assume (uu____3041))
in (

let t_decls = (FStar_List.append decls (FStar_List.append decls' ((tdecl)::(t_kinding)::(t_interp)::(t_haseq)::[])))
in ((FStar_Util.smap_add env.cache tkey_hash ((tsym), (cvar_sorts), (t_decls)));
((t), (t_decls));
)))))))))))))
end))))))))
end))
end))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(

let ttm = (

let uu____3096 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____3096))
in (

let uu____3100 = (encode_term_pred None k env ttm)
in (match (uu____3100) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____3108 = (

let uu____3113 = (

let uu____3115 = (

let uu____3116 = (

let uu____3117 = (

let uu____3118 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____3118))
in (FStar_Util.format1 "uvar_typing_%s" uu____3117))
in (varops.mk_unique uu____3116))
in Some (uu____3115))
in ((t_has_k), (Some ("Uvar typing")), (uu____3113)))
in FStar_SMTEncoding_Term.Assume (uu____3108))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____3125) -> begin
(

let uu____3135 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____3135) with
| (head, args_e) -> begin
(

let uu____3163 = (

let uu____3171 = (

let uu____3172 = (FStar_Syntax_Subst.compress head)
in uu____3172.FStar_Syntax_Syntax.n)
in ((uu____3171), (args_e)))
in (match (uu____3163) with
| (uu____3182, uu____3183) when (head_redex env head) -> begin
(

let uu____3194 = (whnf env t)
in (encode_term uu____3194 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let uu____3268 = (encode_term v1 env)
in (match (uu____3268) with
| (v1, decls1) -> begin
(

let uu____3275 = (encode_term v2 env)
in (match (uu____3275) with
| (v2, decls2) -> begin
(

let uu____3282 = (FStar_SMTEncoding_Util.mk_LexCons v1 v2)
in ((uu____3282), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____3284) -> begin
(

let e0 = (

let uu____3298 = (

let uu____3301 = (

let uu____3302 = (

let uu____3312 = (

let uu____3318 = (FStar_List.hd args_e)
in (uu____3318)::[])
in ((head), (uu____3312)))
in FStar_Syntax_Syntax.Tm_app (uu____3302))
in (FStar_Syntax_Syntax.mk uu____3301))
in (uu____3298 None head.FStar_Syntax_Syntax.pos))
in ((

let uu____3351 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____3351) with
| true -> begin
(

let uu____3352 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Trying to normalize %s\n" uu____3352))
end
| uu____3353 -> begin
()
end));
(

let e0 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv e0)
in ((

let uu____3356 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____3356) with
| true -> begin
(

let uu____3357 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" uu____3357))
end
| uu____3358 -> begin
()
end));
(

let e0 = (

let uu____3360 = (

let uu____3361 = (

let uu____3362 = (FStar_Syntax_Subst.compress e0)
in uu____3362.FStar_Syntax_Syntax.n)
in (match (uu____3361) with
| FStar_Syntax_Syntax.Tm_app (uu____3365) -> begin
false
end
| uu____3375 -> begin
true
end))
in (match (uu____3360) with
| true -> begin
e0
end
| uu____3376 -> begin
(

let uu____3377 = (FStar_Syntax_Util.head_and_args e0)
in (match (uu____3377) with
| (head, args) -> begin
(

let uu____3403 = (

let uu____3404 = (

let uu____3405 = (FStar_Syntax_Subst.compress head)
in uu____3405.FStar_Syntax_Syntax.n)
in (match (uu____3404) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____3408 -> begin
false
end))
in (match (uu____3403) with
| true -> begin
((

let uu____3410 = (Obj.magic (()))
in ());
(

let uu____3411 = (FStar_List.hd args)
in (Prims.fst uu____3411));
)
end
| uu____3422 -> begin
e0
end))
end))
end))
in (

let e = (match (args_e) with
| (uu____3424)::[] -> begin
e0
end
| uu____3437 -> begin
(

let uu____3443 = (

let uu____3446 = (

let uu____3447 = (

let uu____3457 = (FStar_List.tl args_e)
in ((e0), (uu____3457)))
in FStar_Syntax_Syntax.Tm_app (uu____3447))
in (FStar_Syntax_Syntax.mk uu____3446))
in (uu____3443 None t0.FStar_Syntax_Syntax.pos))
end)
in (encode_term e env)));
));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____3480)), ((arg, uu____3482))::[]) -> begin
(encode_term arg env)
end
| uu____3500 -> begin
(

let uu____3508 = (encode_args args_e env)
in (match (uu____3508) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____3541 = (encode_term head env)
in (match (uu____3541) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let uu____3580 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____3580) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun uu____3622 uu____3623 -> (match (((uu____3622), (uu____3623))) with
| ((bv, uu____3637), (a, uu____3639)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (

let uu____3653 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____3653 (FStar_Syntax_Subst.subst subst)))
in (

let uu____3658 = (encode_term_pred None ty env app_tm)
in (match (uu____3658) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____3668 = (

let uu____3673 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____3678 = (

let uu____3680 = (

let uu____3681 = (

let uu____3682 = (

let uu____3683 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____3683))
in (Prims.strcat "partial_app_typing_" uu____3682))
in (varops.mk_unique uu____3681))
in Some (uu____3680))
in ((uu____3673), (Some ("Partial app typing")), (uu____3678))))
in FStar_SMTEncoding_Term.Assume (uu____3668))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____3701 = (lookup_free_var_sym env fv)
in (match (uu____3701) with
| (fname, fuel_args) -> begin
(

let tm = (FStar_SMTEncoding_Util.mkApp' ((fname), ((FStar_List.append fuel_args args))))
in ((tm), (decls)))
end)))
in (

let head = (FStar_Syntax_Subst.compress head)
in (

let head_type = (match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_name (x)) -> begin
Some (x.FStar_Syntax_Syntax.sort)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let uu____3739 = (

let uu____3740 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3740 Prims.snd))
in Some (uu____3739))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3749, FStar_Util.Inl (t), uu____3751) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3772, FStar_Util.Inr (c), uu____3774) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| uu____3795 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (

let uu____3815 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____3815))
in (

let uu____3816 = (curried_arrow_formals_comp head_type)
in (match (uu____3816) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____3841 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (Some (((formals), (c)))))
end
| uu____3853 -> begin
(encode_partial_app None)
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

let uu____3886 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____3886) with
| (bs, body, opening) -> begin
(

let fallback = (fun uu____3901 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (

let uu____3906 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____3906), ((decl)::[]))))))
in (

let is_impure = (fun uu___117_3916 -> (match (uu___117_3916) with
| FStar_Util.Inl (lc) -> begin
(

let uu____3926 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (not (uu____3926)))
end
| FStar_Util.Inr (eff, uu____3928) -> begin
(

let uu____3934 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right uu____3934 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(

let uu____3955 = (

let uu____3956 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____3956))
in (FStar_All.pipe_right uu____3955 (fun _0_31 -> Some (_0_31))))
end
| FStar_Util.Inr (eff, flags) -> begin
(

let new_uvar = (fun uu____3968 -> (

let uu____3969 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____3969 Prims.fst)))
in (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(

let uu____3977 = (

let uu____3978 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total uu____3978))
in (FStar_All.pipe_right uu____3977 (fun _0_32 -> Some (_0_32))))
end
| uu____3980 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(

let uu____3982 = (

let uu____3983 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal uu____3983))
in (FStar_All.pipe_right uu____3982 (fun _0_33 -> Some (_0_33))))
end
| uu____3985 -> begin
None
end)
end))
end))
in (match (lopt) with
| None -> begin
((

let uu____3994 = (

let uu____3995 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____3995))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____3994));
(fallback ());
)
end
| Some (lc) -> begin
(

let uu____4007 = (is_impure lc)
in (match (uu____4007) with
| true -> begin
(fallback ())
end
| uu____4010 -> begin
(

let uu____4011 = (encode_binders None bs env)
in (match (uu____4011) with
| (vars, guards, envbody, decls, uu____4026) -> begin
(

let uu____4033 = (encode_term body envbody)
in (match (uu____4033) with
| (body, decls') -> begin
(

let key_body = (

let uu____4041 = (

let uu____4047 = (

let uu____4048 = (

let uu____4051 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____4051), (body)))
in (FStar_SMTEncoding_Util.mkImp uu____4048))
in (([]), (vars), (uu____4047)))
in (FStar_SMTEncoding_Util.mkForall uu____4041))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____4062 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____4062) with
| Some (t, uu____4077, uu____4078) -> begin
(

let uu____4088 = (

let uu____4089 = (

let uu____4093 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((t), (uu____4093)))
in (FStar_SMTEncoding_Util.mkApp uu____4089))
in ((uu____4088), ([])))
end
| None -> begin
(

let uu____4104 = (is_eta env vars body)
in (match (uu____4104) with
| Some (t) -> begin
((t), ([]))
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let fsym = (

let uu____4115 = (

let uu____4116 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____4116))
in (varops.mk_unique uu____4115))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (

let uu____4121 = (

let uu____4125 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((fsym), (uu____4125)))
in (FStar_SMTEncoding_Util.mkApp uu____4121))
in (

let app = (mk_Apply f vars)
in (

let typing_f = (

let uu____4133 = (codomain_eff lc)
in (match (uu____4133) with
| None -> begin
[]
end
| Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs c)
in (

let uu____4140 = (encode_term_pred None tfun env f)
in (match (uu____4140) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (

let uu____4148 = (

let uu____4150 = (

let uu____4151 = (

let uu____4156 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((uu____4156), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____4151))
in (uu____4150)::[])
in (FStar_List.append decls'' uu____4148)))
end)))
end))
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (

let uu____4166 = (

let uu____4171 = (

let uu____4172 = (

let uu____4178 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (uu____4178)))
in (FStar_SMTEncoding_Util.mkForall uu____4172))
in ((uu____4171), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____4166)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[]))))
in ((FStar_Util.smap_add env.cache tkey_hash ((fsym), (cvar_sorts), (f_decls)));
((f), (f_decls));
)))))))))
end))
end))))))
end))
end))
end))
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((uu____4197, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____4198); FStar_Syntax_Syntax.lbunivs = uu____4199; FStar_Syntax_Syntax.lbtyp = uu____4200; FStar_Syntax_Syntax.lbeff = uu____4201; FStar_Syntax_Syntax.lbdef = uu____4202})::uu____4203), uu____4204) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____4222; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____4224; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____4240) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let uu____4253 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____4253), ((decl_e)::[])))));
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____4295 = (encode_term e1 env)
in (match (uu____4295) with
| (ee1, decls1) -> begin
(

let uu____4302 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (uu____4302) with
| (xs, e2) -> begin
(

let uu____4316 = (FStar_List.hd xs)
in (match (uu____4316) with
| (x, uu____4324) -> begin
(

let env' = (push_term_var env x ee1)
in (

let uu____4326 = (encode_body e2 env')
in (match (uu____4326) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____4348 = (encode_term e env)
in (match (uu____4348) with
| (scr, decls) -> begin
(

let uu____4355 = (FStar_List.fold_right (fun b uu____4363 -> (match (uu____4363) with
| (else_case, decls) -> begin
(

let uu____4374 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____4374) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun uu____4404 uu____4405 -> (match (((uu____4404), (uu____4405))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env uu____4442 -> (match (uu____4442) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let uu____4447 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let uu____4462 = (encode_term w env)
in (match (uu____4462) with
| (w, decls2) -> begin
(

let uu____4470 = (

let uu____4471 = (

let uu____4474 = (

let uu____4475 = (

let uu____4478 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w), (uu____4478)))
in (FStar_SMTEncoding_Util.mkEq uu____4475))
in ((guard), (uu____4474)))
in (FStar_SMTEncoding_Util.mkAnd uu____4471))
in ((uu____4470), (decls2)))
end))
end)
in (match (uu____4447) with
| (guard, decls2) -> begin
(

let uu____4486 = (encode_br br env)
in (match (uu____4486) with
| (br, decls3) -> begin
(

let uu____4494 = (FStar_SMTEncoding_Util.mkITE ((guard), (br), (else_case)))
in ((uu____4494), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (uu____4355) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| uu____4518 -> begin
(

let uu____4519 = (encode_one_pat env pat)
in (uu____4519)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____4531 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4531) with
| true -> begin
(

let uu____4532 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____4532))
end
| uu____4533 -> begin
()
end));
(

let uu____4534 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____4534) with
| (vars, pat_term) -> begin
(

let uu____4544 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____4567 v -> (match (uu____4567) with
| (env, vars) -> begin
(

let uu____4595 = (gen_term_var env v)
in (match (uu____4595) with
| (xx, uu____4607, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (uu____4544) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4654) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____4662 = (

let uu____4665 = (encode_const c)
in ((scrutinee), (uu____4665)))
in (FStar_SMTEncoding_Util.mkEq uu____4662))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4696 -> (match (uu____4696) with
| (arg, uu____4702) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____4712 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____4712)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4731) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____4746) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____4761 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4783 -> (match (uu____4783) with
| (arg, uu____4792) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____4802 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____4802)))
end))))
in (FStar_All.pipe_right uu____4761 FStar_List.flatten))
end))
in (

let pat_term = (fun uu____4818 -> (encode_term pat_term env))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____4825 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____4840 uu____4841 -> (match (((uu____4840), (uu____4841))) with
| ((tms, decls), (t, uu____4861)) -> begin
(

let uu____4872 = (encode_term t env)
in (match (uu____4872) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____4825) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let list_elements = (fun e -> (

let uu____4910 = (FStar_Syntax_Util.list_elements e)
in (match (uu____4910) with
| Some (l) -> begin
l
end
| None -> begin
((FStar_Errors.warn e.FStar_Syntax_Syntax.pos "SMT pattern is not a list literal; ignoring the pattern");
[];
)
end)))
in (

let one_pat = (fun p -> (

let uu____4928 = (

let uu____4938 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____4938 FStar_Syntax_Util.head_and_args))
in (match (uu____4928) with
| (head, args) -> begin
(

let uu____4969 = (

let uu____4977 = (

let uu____4978 = (FStar_Syntax_Util.un_uinst head)
in uu____4978.FStar_Syntax_Syntax.n)
in ((uu____4977), (args)))
in (match (uu____4969) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____4992, uu____4993))::((e, uu____4995))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5026))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| uu____5047 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let uu____5080 = (

let uu____5090 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right uu____5090 FStar_Syntax_Util.head_and_args))
in (match (uu____5080) with
| (head, args) -> begin
(

let uu____5119 = (

let uu____5127 = (

let uu____5128 = (FStar_Syntax_Util.un_uinst head)
in uu____5128.FStar_Syntax_Syntax.n)
in ((uu____5127), (args)))
in (match (uu____5119) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5141))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| uu____5161 -> begin
None
end))
end)))
in (match (elts) with
| (t)::[] -> begin
(

let uu____5179 = (smt_pat_or t)
in (match (uu____5179) with
| Some (e) -> begin
(

let uu____5195 = (list_elements e)
in (FStar_All.pipe_right uu____5195 (FStar_List.map (fun branch -> (

let uu____5212 = (list_elements branch)
in (FStar_All.pipe_right uu____5212 (FStar_List.map one_pat)))))))
end
| uu____5226 -> begin
(

let uu____5230 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5230)::[])
end))
end
| uu____5261 -> begin
(

let uu____5263 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5263)::[])
end))))
in (

let uu____5294 = (

let uu____5310 = (

let uu____5311 = (FStar_Syntax_Subst.compress t)
in uu____5311.FStar_Syntax_Syntax.n)
in (match (uu____5310) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____5341 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____5341) with
| (binders, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____5376; FStar_Syntax_Syntax.effect_name = uu____5377; FStar_Syntax_Syntax.result_typ = uu____5378; FStar_Syntax_Syntax.effect_args = ((pre, uu____5380))::((post, uu____5382))::((pats, uu____5384))::[]; FStar_Syntax_Syntax.flags = uu____5385}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (

let uu____5419 = (lemma_pats pats')
in ((binders), (pre), (post), (uu____5419))))
end
| uu____5438 -> begin
(failwith "impos")
end)
end))
end
| uu____5454 -> begin
(failwith "Impos")
end))
in (match (uu____5294) with
| (binders, pre, post, patterns) -> begin
(

let uu____5498 = (encode_binders None binders env)
in (match (uu____5498) with
| (vars, guards, env, decls, uu____5513) -> begin
(

let uu____5520 = (

let uu____5527 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let uu____5558 = (

let uu____5563 = (FStar_All.pipe_right branch (FStar_List.map (fun uu____5579 -> (match (uu____5579) with
| (t, uu____5586) -> begin
(encode_term t (

let uu___143_5589 = env
in {bindings = uu___143_5589.bindings; depth = uu___143_5589.depth; tcenv = uu___143_5589.tcenv; warn = uu___143_5589.warn; cache = uu___143_5589.cache; nolabels = uu___143_5589.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___143_5589.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right uu____5563 FStar_List.unzip))
in (match (uu____5558) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right uu____5527 FStar_List.unzip))
in (match (uu____5520) with
| (pats, decls') -> begin
(

let decls' = (FStar_List.flatten decls')
in (

let pats = (match (induction_on) with
| None -> begin
pats
end
| Some (e) -> begin
(match (vars) with
| [] -> begin
pats
end
| (l)::[] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (

let uu____5653 = (

let uu____5654 = (FStar_SMTEncoding_Util.mkFreeV l)
in (FStar_SMTEncoding_Util.mk_Precedes uu____5654 e))
in (uu____5653)::p))))
end
| uu____5655 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (

let uu____5684 = (FStar_SMTEncoding_Util.mk_Precedes tl e)
in (uu____5684)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(

let uu____5692 = (

let uu____5693 = (FStar_SMTEncoding_Util.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mk_LexCons uu____5693 tl))
in (aux uu____5692 vars))
end
| uu____5694 -> begin
pats
end))
in (

let uu____5698 = (FStar_SMTEncoding_Util.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux uu____5698 vars)))
end)
end)
in (

let env = (

let uu___144_5700 = env
in {bindings = uu___144_5700.bindings; depth = uu___144_5700.depth; tcenv = uu___144_5700.tcenv; warn = uu___144_5700.warn; cache = uu___144_5700.cache; nolabels = true; use_zfuel_name = uu___144_5700.use_zfuel_name; encode_non_total_function_typ = uu___144_5700.encode_non_total_function_typ})
in (

let uu____5701 = (

let uu____5704 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____5704 env))
in (match (uu____5701) with
| (pre, decls'') -> begin
(

let uu____5709 = (

let uu____5712 = (FStar_Syntax_Util.unmeta post)
in (encode_formula uu____5712 env))
in (match (uu____5709) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (

let uu____5719 = (

let uu____5720 = (

let uu____5726 = (

let uu____5727 = (

let uu____5730 = (FStar_SMTEncoding_Util.mk_and_l ((pre)::guards))
in ((uu____5730), (post)))
in (FStar_SMTEncoding_Util.mkImp uu____5727))
in ((pats), (vars), (uu____5726)))
in (FStar_SMTEncoding_Util.mkForall uu____5720))
in ((uu____5719), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> (

let uu____5743 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____5743) with
| true -> begin
(

let uu____5744 = (FStar_Syntax_Print.tag_of_term phi)
in (

let uu____5745 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____5744 uu____5745)))
end
| uu____5746 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____5772 = (FStar_Util.fold_map (fun decls x -> (

let uu____5785 = (encode_term (Prims.fst x) env)
in (match (uu____5785) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____5772) with
| (decls, args) -> begin
(

let uu____5802 = (

let uu___145_5803 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___145_5803.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___145_5803.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____5802), (decls)))
end)))
in (

let const_op = (fun f r uu____5822 -> (

let uu____5825 = (f r)
in ((uu____5825), ([]))))
in (

let un_op = (fun f l -> (

let uu____5841 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____5841)))
in (

let bin_op = (fun f uu___118_5854 -> (match (uu___118_5854) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____5862 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____5889 = (FStar_Util.fold_map (fun decls uu____5898 -> (match (uu____5898) with
| (t, uu____5906) -> begin
(

let uu____5907 = (encode_formula t env)
in (match (uu____5907) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (uu____5889) with
| (decls, phis) -> begin
(

let uu____5924 = (

let uu___146_5925 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___146_5925.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___146_5925.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____5924), (decls)))
end)))
in (

let eq_op = (fun r uu___119_5941 -> (match (uu___119_5941) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
((enc (bin_op FStar_SMTEncoding_Util.mkEq)) r ((e1)::(e2)::[]))
end
| l -> begin
((enc (bin_op FStar_SMTEncoding_Util.mkEq)) r l)
end))
in (

let mk_imp = (fun r uu___120_6026 -> (match (uu___120_6026) with
| ((lhs, uu____6030))::((rhs, uu____6032))::[] -> begin
(

let uu____6053 = (encode_formula rhs env)
in (match (uu____6053) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____6062) -> begin
((l1), (decls1))
end
| uu____6065 -> begin
(

let uu____6066 = (encode_formula lhs env)
in (match (uu____6066) with
| (l2, decls2) -> begin
(

let uu____6073 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____6073), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____6075 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___121_6090 -> (match (uu___121_6090) with
| ((guard, uu____6094))::((_then, uu____6096))::((_else, uu____6098))::[] -> begin
(

let uu____6127 = (encode_formula guard env)
in (match (uu____6127) with
| (g, decls1) -> begin
(

let uu____6134 = (encode_formula _then env)
in (match (uu____6134) with
| (t, decls2) -> begin
(

let uu____6141 = (encode_formula _else env)
in (match (uu____6141) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____6150 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____6169 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____6169)))
in (

let connectives = (

let uu____6181 = (

let uu____6190 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Syntax_Const.and_lid), (uu____6190)))
in (

let uu____6212 = (

let uu____6222 = (

let uu____6231 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Syntax_Const.or_lid), (uu____6231)))
in (

let uu____6253 = (

let uu____6263 = (

let uu____6273 = (

let uu____6282 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Syntax_Const.iff_lid), (uu____6282)))
in (

let uu____6304 = (

let uu____6314 = (

let uu____6324 = (

let uu____6333 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Syntax_Const.not_lid), (uu____6333)))
in (uu____6324)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::uu____6314)
in (uu____6273)::uu____6304))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::uu____6263)
in (uu____6222)::uu____6253))
in (uu____6181)::uu____6212))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____6504 = (encode_formula phi' env)
in (match (uu____6504) with
| (phi, decls) -> begin
(

let uu____6511 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))) r)
in ((uu____6511), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____6512) -> begin
(

let uu____6517 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula uu____6517 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____6546 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____6546) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____6554; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____6556; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____6572 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____6572) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____6604)::((x, uu____6606))::((t, uu____6608))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let uu____6642 = (encode_term x env)
in (match (uu____6642) with
| (x, decls) -> begin
(

let uu____6649 = (encode_term t env)
in (match (uu____6649) with
| (t, decls') -> begin
(

let uu____6656 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((uu____6656), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____6660))::((msg, uu____6662))::((phi, uu____6664))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(

let uu____6698 = (

let uu____6701 = (

let uu____6702 = (FStar_Syntax_Subst.compress r)
in uu____6702.FStar_Syntax_Syntax.n)
in (

let uu____6705 = (

let uu____6706 = (FStar_Syntax_Subst.compress msg)
in uu____6706.FStar_Syntax_Syntax.n)
in ((uu____6701), (uu____6705))))
in (match (uu____6698) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____6713))) -> begin
(

let phi = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false)))))))) None r)
in (fallback phi))
end
| uu____6729 -> begin
(fallback phi)
end))
end
| uu____6732 when (head_redex env head) -> begin
(

let uu____6740 = (whnf env phi)
in (encode_formula uu____6740 env))
end
| uu____6741 -> begin
(

let uu____6749 = (encode_term phi env)
in (match (uu____6749) with
| (tt, decls) -> begin
(

let uu____6756 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___147_6757 = tt
in {FStar_SMTEncoding_Term.tm = uu___147_6757.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___147_6757.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((uu____6756), (decls)))
end))
end))
end
| uu____6760 -> begin
(

let uu____6761 = (encode_term phi env)
in (match (uu____6761) with
| (tt, decls) -> begin
(

let uu____6768 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___148_6769 = tt
in {FStar_SMTEncoding_Term.tm = uu___148_6769.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___148_6769.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((uu____6768), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let uu____6796 = (encode_binders None bs env)
in (match (uu____6796) with
| (vars, guards, env, decls, uu____6818) -> begin
(

let uu____6825 = (

let uu____6832 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____6855 = (

let uu____6860 = (FStar_All.pipe_right p (FStar_List.map (fun uu____6874 -> (match (uu____6874) with
| (t, uu____6880) -> begin
(encode_term t (

let uu___149_6881 = env
in {bindings = uu___149_6881.bindings; depth = uu___149_6881.depth; tcenv = uu___149_6881.tcenv; warn = uu___149_6881.warn; cache = uu___149_6881.cache; nolabels = uu___149_6881.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___149_6881.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right uu____6860 FStar_List.unzip))
in (match (uu____6855) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right uu____6832 FStar_List.unzip))
in (match (uu____6825) with
| (pats, decls') -> begin
(

let uu____6933 = (encode_formula body env)
in (match (uu____6933) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____6952; FStar_SMTEncoding_Term.rng = uu____6953})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| uu____6961 -> begin
guards
end)
in (

let uu____6964 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((vars), (pats), (uu____6964), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug phi);
(

let phi = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun uu____6998 -> (match (uu____6998) with
| (x, uu____7002) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats) with
| [] -> begin
()
end
| (hd)::tl -> begin
(

let pat_vars = (

let uu____7008 = (FStar_Syntax_Free.names hd)
in (FStar_List.fold_left (fun out x -> (

let uu____7014 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____7014))) uu____7008 tl))
in (

let uu____7016 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____7028 -> (match (uu____7028) with
| (b, uu____7032) -> begin
(

let uu____7033 = (FStar_Util.set_mem b pat_vars)
in (not (uu____7033)))
end))))
in (match (uu____7016) with
| None -> begin
()
end
| Some (x, uu____7037) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd.FStar_Syntax_Syntax.pos tl)
in (

let uu____7047 = (

let uu____7048 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____7048))
in (FStar_Errors.warn pos uu____7047)))
end)))
end)))
in (

let uu____7049 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____7049) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____7055 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____7091 -> (match (uu____7091) with
| (l, uu____7101) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____7055) with
| None -> begin
(fallback phi)
end
| Some (uu____7124, f) -> begin
(f phi.FStar_Syntax_Syntax.pos arms)
end))
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7153 = (encode_q_body env vars pats body)
in (match (uu____7153) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (

let uu____7179 = (

let uu____7185 = (FStar_SMTEncoding_Util.mkImp ((guard), (body)))
in ((pats), (vars), (uu____7185)))
in (FStar_SMTEncoding_Term.mkForall uu____7179 phi.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7197 = (encode_q_body env vars pats body)
in (match (uu____7197) with
| (vars, pats, guard, body, decls) -> begin
(

let uu____7222 = (

let uu____7223 = (

let uu____7229 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body)))
in ((pats), (vars), (uu____7229)))
in (FStar_SMTEncoding_Term.mkExists uu____7223 phi.FStar_Syntax_Syntax.pos))
in ((uu____7222), (decls)))
end));
)
end))));
)))))))))))))))

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let prims : prims_t = (

let uu____7278 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7278) with
| (asym, a) -> begin
(

let uu____7283 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7283) with
| (xsym, x) -> begin
(

let uu____7288 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7288) with
| (ysym, y) -> begin
(

let quant = (fun vars body x -> (

let xname_decl = (

let uu____7318 = (

let uu____7324 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (uu____7324), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____7318))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (

let uu____7339 = (

let uu____7343 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x), (uu____7343)))
in (FStar_SMTEncoding_Util.mkApp uu____7339))
in (

let xtok = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (

let uu____7351 = (

let uu____7353 = (

let uu____7355 = (

let uu____7357 = (

let uu____7358 = (

let uu____7363 = (

let uu____7364 = (

let uu____7370 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____7370)))
in (FStar_SMTEncoding_Util.mkForall uu____7364))
in ((uu____7363), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (uu____7358))
in (

let uu____7380 = (

let uu____7382 = (

let uu____7383 = (

let uu____7388 = (

let uu____7389 = (

let uu____7395 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____7395)))
in (FStar_SMTEncoding_Util.mkForall uu____7389))
in ((uu____7388), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x)))))
in FStar_SMTEncoding_Term.Assume (uu____7383))
in (uu____7382)::[])
in (uu____7357)::uu____7380))
in (xtok_decl)::uu____7355)
in (xname_decl)::uu____7353)
in ((xtok), (uu____7351))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (

let uu____7445 = (

let uu____7453 = (

let uu____7459 = (

let uu____7460 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7460))
in (quant axy uu____7459))
in ((FStar_Syntax_Const.op_Eq), (uu____7453)))
in (

let uu____7466 = (

let uu____7475 = (

let uu____7483 = (

let uu____7489 = (

let uu____7490 = (

let uu____7491 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____7491))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7490))
in (quant axy uu____7489))
in ((FStar_Syntax_Const.op_notEq), (uu____7483)))
in (

let uu____7497 = (

let uu____7506 = (

let uu____7514 = (

let uu____7520 = (

let uu____7521 = (

let uu____7522 = (

let uu____7525 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7526 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7525), (uu____7526))))
in (FStar_SMTEncoding_Util.mkLT uu____7522))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7521))
in (quant xy uu____7520))
in ((FStar_Syntax_Const.op_LT), (uu____7514)))
in (

let uu____7532 = (

let uu____7541 = (

let uu____7549 = (

let uu____7555 = (

let uu____7556 = (

let uu____7557 = (

let uu____7560 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7561 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7560), (uu____7561))))
in (FStar_SMTEncoding_Util.mkLTE uu____7557))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7556))
in (quant xy uu____7555))
in ((FStar_Syntax_Const.op_LTE), (uu____7549)))
in (

let uu____7567 = (

let uu____7576 = (

let uu____7584 = (

let uu____7590 = (

let uu____7591 = (

let uu____7592 = (

let uu____7595 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7596 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7595), (uu____7596))))
in (FStar_SMTEncoding_Util.mkGT uu____7592))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7591))
in (quant xy uu____7590))
in ((FStar_Syntax_Const.op_GT), (uu____7584)))
in (

let uu____7602 = (

let uu____7611 = (

let uu____7619 = (

let uu____7625 = (

let uu____7626 = (

let uu____7627 = (

let uu____7630 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7631 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7630), (uu____7631))))
in (FStar_SMTEncoding_Util.mkGTE uu____7627))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7626))
in (quant xy uu____7625))
in ((FStar_Syntax_Const.op_GTE), (uu____7619)))
in (

let uu____7637 = (

let uu____7646 = (

let uu____7654 = (

let uu____7660 = (

let uu____7661 = (

let uu____7662 = (

let uu____7665 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7666 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7665), (uu____7666))))
in (FStar_SMTEncoding_Util.mkSub uu____7662))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7661))
in (quant xy uu____7660))
in ((FStar_Syntax_Const.op_Subtraction), (uu____7654)))
in (

let uu____7672 = (

let uu____7681 = (

let uu____7689 = (

let uu____7695 = (

let uu____7696 = (

let uu____7697 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____7697))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7696))
in (quant qx uu____7695))
in ((FStar_Syntax_Const.op_Minus), (uu____7689)))
in (

let uu____7703 = (

let uu____7712 = (

let uu____7720 = (

let uu____7726 = (

let uu____7727 = (

let uu____7728 = (

let uu____7731 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7732 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7731), (uu____7732))))
in (FStar_SMTEncoding_Util.mkAdd uu____7728))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7727))
in (quant xy uu____7726))
in ((FStar_Syntax_Const.op_Addition), (uu____7720)))
in (

let uu____7738 = (

let uu____7747 = (

let uu____7755 = (

let uu____7761 = (

let uu____7762 = (

let uu____7763 = (

let uu____7766 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7767 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7766), (uu____7767))))
in (FStar_SMTEncoding_Util.mkMul uu____7763))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7762))
in (quant xy uu____7761))
in ((FStar_Syntax_Const.op_Multiply), (uu____7755)))
in (

let uu____7773 = (

let uu____7782 = (

let uu____7790 = (

let uu____7796 = (

let uu____7797 = (

let uu____7798 = (

let uu____7801 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7802 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7801), (uu____7802))))
in (FStar_SMTEncoding_Util.mkDiv uu____7798))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7797))
in (quant xy uu____7796))
in ((FStar_Syntax_Const.op_Division), (uu____7790)))
in (

let uu____7808 = (

let uu____7817 = (

let uu____7825 = (

let uu____7831 = (

let uu____7832 = (

let uu____7833 = (

let uu____7836 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7837 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7836), (uu____7837))))
in (FStar_SMTEncoding_Util.mkMod uu____7833))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7832))
in (quant xy uu____7831))
in ((FStar_Syntax_Const.op_Modulus), (uu____7825)))
in (

let uu____7843 = (

let uu____7852 = (

let uu____7860 = (

let uu____7866 = (

let uu____7867 = (

let uu____7868 = (

let uu____7871 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____7872 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____7871), (uu____7872))))
in (FStar_SMTEncoding_Util.mkAnd uu____7868))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7867))
in (quant xy uu____7866))
in ((FStar_Syntax_Const.op_And), (uu____7860)))
in (

let uu____7878 = (

let uu____7887 = (

let uu____7895 = (

let uu____7901 = (

let uu____7902 = (

let uu____7903 = (

let uu____7906 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____7907 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____7906), (uu____7907))))
in (FStar_SMTEncoding_Util.mkOr uu____7903))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7902))
in (quant xy uu____7901))
in ((FStar_Syntax_Const.op_Or), (uu____7895)))
in (

let uu____7913 = (

let uu____7922 = (

let uu____7930 = (

let uu____7936 = (

let uu____7937 = (

let uu____7938 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____7938))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7937))
in (quant qx uu____7936))
in ((FStar_Syntax_Const.op_Negation), (uu____7930)))
in (uu____7922)::[])
in (uu____7887)::uu____7913))
in (uu____7852)::uu____7878))
in (uu____7817)::uu____7843))
in (uu____7782)::uu____7808))
in (uu____7747)::uu____7773))
in (uu____7712)::uu____7738))
in (uu____7681)::uu____7703))
in (uu____7646)::uu____7672))
in (uu____7611)::uu____7637))
in (uu____7576)::uu____7602))
in (uu____7541)::uu____7567))
in (uu____7506)::uu____7532))
in (uu____7475)::uu____7497))
in (uu____7445)::uu____7466))
in (

let mk = (fun l v -> (

let uu____8066 = (

let uu____8071 = (FStar_All.pipe_right prims (FStar_List.find (fun uu____8103 -> (match (uu____8103) with
| (l', uu____8112) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____8071 (FStar_Option.map (fun uu____8145 -> (match (uu____8145) with
| (uu____8156, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right uu____8066 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun uu____8197 -> (match (uu____8197) with
| (l', uu____8206) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let uu____8229 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____8229) with
| (xxsym, xx) -> begin
(

let uu____8234 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____8234) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let uu____8241 = (

let uu____8246 = (

let uu____8247 = (

let uu____8253 = (

let uu____8254 = (

let uu____8257 = (

let uu____8258 = (

let uu____8261 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____8261)))
in (FStar_SMTEncoding_Util.mkEq uu____8258))
in ((xx_has_type), (uu____8257)))
in (FStar_SMTEncoding_Util.mkImp uu____8254))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____8253)))
in (FStar_SMTEncoding_Util.mkForall uu____8247))
in (

let uu____8274 = (

let uu____8276 = (

let uu____8277 = (

let uu____8278 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "pretyping_" uu____8278))
in (varops.mk_unique uu____8277))
in Some (uu____8276))
in ((uu____8246), (Some ("pretyping")), (uu____8274))))
in FStar_SMTEncoding_Term.Assume (uu____8241))))
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

let uu____8309 = (

let uu____8310 = (

let uu____8315 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____8315), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8310))
in (

let uu____8318 = (

let uu____8320 = (

let uu____8321 = (

let uu____8326 = (

let uu____8327 = (

let uu____8333 = (

let uu____8334 = (

let uu____8337 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____8337)))
in (FStar_SMTEncoding_Util.mkImp uu____8334))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8333)))
in (mkForall_fuel uu____8327))
in ((uu____8326), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8321))
in (uu____8320)::[])
in (uu____8309)::uu____8318))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8366 = (

let uu____8367 = (

let uu____8372 = (

let uu____8373 = (

let uu____8379 = (

let uu____8382 = (

let uu____8384 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____8384)::[])
in (uu____8382)::[])
in (

let uu____8387 = (

let uu____8388 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8388 tt))
in ((uu____8379), ((bb)::[]), (uu____8387))))
in (FStar_SMTEncoding_Util.mkForall uu____8373))
in ((uu____8372), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8367))
in (

let uu____8400 = (

let uu____8402 = (

let uu____8403 = (

let uu____8408 = (

let uu____8409 = (

let uu____8415 = (

let uu____8416 = (

let uu____8419 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (uu____8419)))
in (FStar_SMTEncoding_Util.mkImp uu____8416))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8415)))
in (mkForall_fuel uu____8409))
in ((uu____8408), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8403))
in (uu____8402)::[])
in (uu____8366)::uu____8400))))))
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

let uu____8454 = (

let uu____8455 = (

let uu____8459 = (

let uu____8461 = (

let uu____8463 = (

let uu____8465 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____8466 = (

let uu____8468 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8468)::[])
in (uu____8465)::uu____8466))
in (tt)::uu____8463)
in (tt)::uu____8461)
in (("Prims.Precedes"), (uu____8459)))
in (FStar_SMTEncoding_Util.mkApp uu____8455))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8454))
in (

let precedes_y_x = (

let uu____8471 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8471))
in (

let uu____8473 = (

let uu____8474 = (

let uu____8479 = (

let uu____8480 = (

let uu____8486 = (

let uu____8489 = (

let uu____8491 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8491)::[])
in (uu____8489)::[])
in (

let uu____8494 = (

let uu____8495 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8495 tt))
in ((uu____8486), ((bb)::[]), (uu____8494))))
in (FStar_SMTEncoding_Util.mkForall uu____8480))
in ((uu____8479), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8474))
in (

let uu____8507 = (

let uu____8509 = (

let uu____8510 = (

let uu____8515 = (

let uu____8516 = (

let uu____8522 = (

let uu____8523 = (

let uu____8526 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (uu____8526)))
in (FStar_SMTEncoding_Util.mkImp uu____8523))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8522)))
in (mkForall_fuel uu____8516))
in ((uu____8515), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8510))
in (

let uu____8540 = (

let uu____8542 = (

let uu____8543 = (

let uu____8548 = (

let uu____8549 = (

let uu____8555 = (

let uu____8556 = (

let uu____8559 = (

let uu____8560 = (

let uu____8562 = (

let uu____8564 = (

let uu____8566 = (

let uu____8567 = (

let uu____8570 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____8571 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8570), (uu____8571))))
in (FStar_SMTEncoding_Util.mkGT uu____8567))
in (

let uu____8572 = (

let uu____8574 = (

let uu____8575 = (

let uu____8578 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8579 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8578), (uu____8579))))
in (FStar_SMTEncoding_Util.mkGTE uu____8575))
in (

let uu____8580 = (

let uu____8582 = (

let uu____8583 = (

let uu____8586 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8587 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____8586), (uu____8587))))
in (FStar_SMTEncoding_Util.mkLT uu____8583))
in (uu____8582)::[])
in (uu____8574)::uu____8580))
in (uu____8566)::uu____8572))
in (typing_pred_y)::uu____8564)
in (typing_pred)::uu____8562)
in (FStar_SMTEncoding_Util.mk_and_l uu____8560))
in ((uu____8559), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____8556))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____8555)))
in (mkForall_fuel uu____8549))
in ((uu____8548), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (uu____8543))
in (uu____8542)::[])
in (uu____8509)::uu____8540))
in (uu____8473)::uu____8507)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8618 = (

let uu____8619 = (

let uu____8624 = (

let uu____8625 = (

let uu____8631 = (

let uu____8634 = (

let uu____8636 = (FStar_SMTEncoding_Term.boxString b)
in (uu____8636)::[])
in (uu____8634)::[])
in (

let uu____8639 = (

let uu____8640 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8640 tt))
in ((uu____8631), ((bb)::[]), (uu____8639))))
in (FStar_SMTEncoding_Util.mkForall uu____8625))
in ((uu____8624), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8619))
in (

let uu____8652 = (

let uu____8654 = (

let uu____8655 = (

let uu____8660 = (

let uu____8661 = (

let uu____8667 = (

let uu____8668 = (

let uu____8671 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (uu____8671)))
in (FStar_SMTEncoding_Util.mkImp uu____8668))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8667)))
in (mkForall_fuel uu____8661))
in ((uu____8660), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8655))
in (uu____8654)::[])
in (uu____8618)::uu____8652))))))
in (

let mk_ref = (fun env reft_name uu____8694 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (

let uu____8705 = (

let uu____8709 = (

let uu____8711 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (uu____8711)::[])
in ((reft_name), (uu____8709)))
in (FStar_SMTEncoding_Util.mkApp uu____8705))
in (

let refb = (

let uu____8714 = (

let uu____8718 = (

let uu____8720 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (uu____8720)::[])
in ((reft_name), (uu____8718)))
in (FStar_SMTEncoding_Util.mkApp uu____8714))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (

let uu____8724 = (

let uu____8725 = (

let uu____8730 = (

let uu____8731 = (

let uu____8737 = (

let uu____8738 = (

let uu____8741 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (uu____8741)))
in (FStar_SMTEncoding_Util.mkImp uu____8738))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (uu____8737)))
in (mkForall_fuel uu____8731))
in ((uu____8730), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8725))
in (

let uu____8757 = (

let uu____8759 = (

let uu____8760 = (

let uu____8765 = (

let uu____8766 = (

let uu____8772 = (

let uu____8773 = (

let uu____8776 = (FStar_SMTEncoding_Util.mkAnd ((typing_pred), (typing_pred_b)))
in (

let uu____8777 = (

let uu____8778 = (

let uu____8781 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let uu____8782 = (FStar_SMTEncoding_Util.mkFreeV bb)
in ((uu____8781), (uu____8782))))
in (FStar_SMTEncoding_Util.mkEq uu____8778))
in ((uu____8776), (uu____8777))))
in (FStar_SMTEncoding_Util.mkImp uu____8773))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (uu____8772)))
in (mkForall_fuel' (Prims.parse_int "2") uu____8766))
in ((uu____8765), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (uu____8760))
in (uu____8759)::[])
in (uu____8724)::uu____8757))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), (Some ("true_interp")))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____8826 = (

let uu____8827 = (

let uu____8832 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____8832), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8827))
in (uu____8826)::[])))
in (

let mk_and_interp = (fun env conj uu____8844 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____8854 = (

let uu____8858 = (

let uu____8860 = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (uu____8860)::[])
in (("Valid"), (uu____8858)))
in (FStar_SMTEncoding_Util.mkApp uu____8854))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____8867 = (

let uu____8868 = (

let uu____8873 = (

let uu____8874 = (

let uu____8880 = (

let uu____8881 = (

let uu____8884 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____8884), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____8881))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____8880)))
in (FStar_SMTEncoding_Util.mkForall uu____8874))
in ((uu____8873), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8868))
in (uu____8867)::[])))))))))
in (

let mk_or_interp = (fun env disj uu____8909 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____8919 = (

let uu____8923 = (

let uu____8925 = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (uu____8925)::[])
in (("Valid"), (uu____8923)))
in (FStar_SMTEncoding_Util.mkApp uu____8919))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____8932 = (

let uu____8933 = (

let uu____8938 = (

let uu____8939 = (

let uu____8945 = (

let uu____8946 = (

let uu____8949 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____8949), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____8946))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____8945)))
in (FStar_SMTEncoding_Util.mkForall uu____8939))
in ((uu____8938), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8933))
in (uu____8932)::[])))))))))
in (

let mk_eq2_interp = (fun env eq2 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let y = (FStar_SMTEncoding_Util.mkFreeV yy)
in (

let valid = (

let uu____8988 = (

let uu____8992 = (

let uu____8994 = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (uu____8994)::[])
in (("Valid"), (uu____8992)))
in (FStar_SMTEncoding_Util.mkApp uu____8988))
in (

let uu____8997 = (

let uu____8998 = (

let uu____9003 = (

let uu____9004 = (

let uu____9010 = (

let uu____9011 = (

let uu____9014 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((uu____9014), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9011))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (uu____9010)))
in (FStar_SMTEncoding_Util.mkForall uu____9004))
in ((uu____9003), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8998))
in (uu____8997)::[])))))))))
in (

let mk_eq3_interp = (fun env eq3 tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let yy = (("y"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let y = (FStar_SMTEncoding_Util.mkFreeV yy)
in (

let valid = (

let uu____9059 = (

let uu____9063 = (

let uu____9065 = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (uu____9065)::[])
in (("Valid"), (uu____9063)))
in (FStar_SMTEncoding_Util.mkApp uu____9059))
in (

let uu____9068 = (

let uu____9069 = (

let uu____9074 = (

let uu____9075 = (

let uu____9081 = (

let uu____9082 = (

let uu____9085 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((uu____9085), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9082))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (uu____9081)))
in (FStar_SMTEncoding_Util.mkForall uu____9075))
in ((uu____9074), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9069))
in (uu____9068)::[])))))))))))
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

let valid = (

let uu____9124 = (

let uu____9128 = (

let uu____9130 = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (uu____9130)::[])
in (("Valid"), (uu____9128)))
in (FStar_SMTEncoding_Util.mkApp uu____9124))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9137 = (

let uu____9138 = (

let uu____9143 = (

let uu____9144 = (

let uu____9150 = (

let uu____9151 = (

let uu____9154 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____9154), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9151))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9150)))
in (FStar_SMTEncoding_Util.mkForall uu____9144))
in ((uu____9143), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9138))
in (uu____9137)::[])))))))))
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

let valid = (

let uu____9189 = (

let uu____9193 = (

let uu____9195 = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (uu____9195)::[])
in (("Valid"), (uu____9193)))
in (FStar_SMTEncoding_Util.mkApp uu____9189))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9202 = (

let uu____9203 = (

let uu____9208 = (

let uu____9209 = (

let uu____9215 = (

let uu____9216 = (

let uu____9219 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____9219), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9216))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9215)))
in (FStar_SMTEncoding_Util.mkForall uu____9209))
in ((uu____9208), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9203))
in (uu____9202)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let valid = (

let uu____9250 = (

let uu____9254 = (

let uu____9256 = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (uu____9256)::[])
in (("Valid"), (uu____9254)))
in (FStar_SMTEncoding_Util.mkApp uu____9250))
in (

let not_valid_a = (

let uu____9260 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9260))
in (

let uu____9262 = (

let uu____9263 = (

let uu____9268 = (

let uu____9269 = (

let uu____9275 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (uu____9275)))
in (FStar_SMTEncoding_Util.mkForall uu____9269))
in ((uu____9268), (Some ("not interpretation")), (Some ("l_not-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9263))
in (uu____9262)::[]))))))
in (

let mk_forall_interp = (fun env for_all tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid = (

let uu____9312 = (

let uu____9316 = (

let uu____9318 = (FStar_SMTEncoding_Util.mkApp ((for_all), ((a)::(b)::[])))
in (uu____9318)::[])
in (("Valid"), (uu____9316)))
in (FStar_SMTEncoding_Util.mkApp uu____9312))
in (

let valid_b_x = (

let uu____9322 = (

let uu____9326 = (

let uu____9328 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (uu____9328)::[])
in (("Valid"), (uu____9326)))
in (FStar_SMTEncoding_Util.mkApp uu____9322))
in (

let uu____9330 = (

let uu____9331 = (

let uu____9336 = (

let uu____9337 = (

let uu____9343 = (

let uu____9344 = (

let uu____9347 = (

let uu____9348 = (

let uu____9354 = (

let uu____9357 = (

let uu____9359 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (uu____9359)::[])
in (uu____9357)::[])
in (

let uu____9362 = (

let uu____9363 = (

let uu____9366 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((uu____9366), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9363))
in ((uu____9354), ((xx)::[]), (uu____9362))))
in (FStar_SMTEncoding_Util.mkForall uu____9348))
in ((uu____9347), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9344))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9343)))
in (FStar_SMTEncoding_Util.mkForall uu____9337))
in ((uu____9336), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9331))
in (uu____9330)::[]))))))))))
in (

let mk_exists_interp = (fun env for_some tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid = (

let uu____9414 = (

let uu____9418 = (

let uu____9420 = (FStar_SMTEncoding_Util.mkApp ((for_some), ((a)::(b)::[])))
in (uu____9420)::[])
in (("Valid"), (uu____9418)))
in (FStar_SMTEncoding_Util.mkApp uu____9414))
in (

let valid_b_x = (

let uu____9424 = (

let uu____9428 = (

let uu____9430 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (uu____9430)::[])
in (("Valid"), (uu____9428)))
in (FStar_SMTEncoding_Util.mkApp uu____9424))
in (

let uu____9432 = (

let uu____9433 = (

let uu____9438 = (

let uu____9439 = (

let uu____9445 = (

let uu____9446 = (

let uu____9449 = (

let uu____9450 = (

let uu____9456 = (

let uu____9459 = (

let uu____9461 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (uu____9461)::[])
in (uu____9459)::[])
in (

let uu____9464 = (

let uu____9465 = (

let uu____9468 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((uu____9468), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9465))
in ((uu____9456), ((xx)::[]), (uu____9464))))
in (FStar_SMTEncoding_Util.mkExists uu____9450))
in ((uu____9449), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9446))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9445)))
in (FStar_SMTEncoding_Util.mkForall uu____9439))
in ((uu____9438), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9433))
in (uu____9432)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____9505 = (

let uu____9506 = (

let uu____9511 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (

let uu____9512 = (

let uu____9514 = (varops.mk_unique "typing_range_const")
in Some (uu____9514))
in ((uu____9511), (Some ("Range_const typing")), (uu____9512))))
in FStar_SMTEncoding_Term.Assume (uu____9506))
in (uu____9505)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (

let uu____9777 = (FStar_Util.find_opt (fun uu____9795 -> (match (uu____9795) with
| (l, uu____9805) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)
in (match (uu____9777) with
| None -> begin
[]
end
| Some (uu____9827, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9864 = (encode_function_type_as_formula None None t env)
in (match (uu____9864) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9897 = ((

let uu____9898 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation uu____9898)) || (FStar_Syntax_Util.is_lemma t_norm))
in (match (uu____9897) with
| true -> begin
(

let uu____9902 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____9902) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (

let uu____9914 = (

let uu____9915 = (FStar_Syntax_Subst.compress t_norm)
in uu____9915.FStar_Syntax_Syntax.n)
in (match (uu____9914) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____9920) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____9937 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____9940 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env)))))
end))
end
| uu____9948 -> begin
(

let uu____9949 = (prims.is lid)
in (match (uu____9949) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____9954 = (prims.mk lid vname)
in (match (uu____9954) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end
| uu____9967 -> begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let uu____9969 = (

let uu____9975 = (curried_arrow_formals_comp t_norm)
in (match (uu____9975) with
| (args, comp) -> begin
(match (encode_non_total_function_typ) with
| true -> begin
(

let uu____9990 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (uu____9990)))
end
| uu____9997 -> begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end)
end))
in (match (uu____9969) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____10017 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____10017) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____10030 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___122_10054 -> (match (uu___122_10054) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____10057 = (FStar_Util.prefix vars)
in (match (uu____10057) with
| (uu____10068, (xxsym, uu____10070)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____10080 = (

let uu____10081 = (

let uu____10086 = (

let uu____10087 = (

let uu____10093 = (

let uu____10094 = (

let uu____10097 = (

let uu____10098 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____10098))
in ((vapp), (uu____10097)))
in (FStar_SMTEncoding_Util.mkEq uu____10094))
in ((((vapp)::[])::[]), (vars), (uu____10093)))
in (FStar_SMTEncoding_Util.mkForall uu____10087))
in ((uu____10086), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (uu____10081))
in (uu____10080)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____10110 = (FStar_Util.prefix vars)
in (match (uu____10110) with
| (uu____10121, (xxsym, uu____10123)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____10137 = (

let uu____10138 = (

let uu____10143 = (

let uu____10144 = (

let uu____10150 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____10150)))
in (FStar_SMTEncoding_Util.mkForall uu____10144))
in ((uu____10143), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (uu____10138))
in (uu____10137)::[])))))
end))
end
| uu____10160 -> begin
[]
end)))))
in (

let uu____10161 = (encode_binders None formals env)
in (match (uu____10161) with
| (vars, guards, env', decls1, uu____10177) -> begin
(

let uu____10184 = (match (pre_opt) with
| None -> begin
(

let uu____10189 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____10189), (decls1)))
end
| Some (p) -> begin
(

let uu____10191 = (encode_formula p env')
in (match (uu____10191) with
| (g, ds) -> begin
(

let uu____10198 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____10198), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____10184) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____10207 = (

let uu____10211 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____10211)))
in (FStar_SMTEncoding_Util.mkApp uu____10207))
in (

let uu____10216 = (

let vname_decl = (

let uu____10221 = (

let uu____10227 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____10232 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____10227), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____10221))
in (

let uu____10237 = (

let env = (

let uu___150_10241 = env
in {bindings = uu___150_10241.bindings; depth = uu___150_10241.depth; tcenv = uu___150_10241.tcenv; warn = uu___150_10241.warn; cache = uu___150_10241.cache; nolabels = uu___150_10241.nolabels; use_zfuel_name = uu___150_10241.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (

let uu____10242 = (

let uu____10243 = (head_normal env tt)
in (not (uu____10243)))
in (match (uu____10242) with
| true -> begin
(encode_term_pred None tt env vtok_tm)
end
| uu____10246 -> begin
(encode_term_pred None t_norm env vtok_tm)
end)))
in (match (uu____10237) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let uu____10255 = (match (formals) with
| [] -> begin
(

let uu____10264 = (

let uu____10265 = (

let uu____10267 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_34 -> Some (_0_34)) uu____10267))
in (push_free_var env lid vname uu____10265))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (uu____10264)))
end
| uu____10270 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (

let uu____10275 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) uu____10275))
in (

let name_tok_corr = (

let uu____10277 = (

let uu____10282 = (

let uu____10283 = (

let uu____10289 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____10289)))
in (FStar_SMTEncoding_Util.mkForall uu____10283))
in ((uu____10282), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (uu____10277))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (uu____10255) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (uu____10216) with
| (decls2, env) -> begin
(

let uu____10314 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let uu____10319 = (encode_term res_t env')
in (match (uu____10319) with
| (encoded_res_t, decls) -> begin
(

let uu____10327 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____10327), (decls)))
end)))
in (match (uu____10314) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____10335 = (

let uu____10340 = (

let uu____10341 = (

let uu____10347 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____10347)))
in (FStar_SMTEncoding_Util.mkForall uu____10341))
in ((uu____10340), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (uu____10335))
in (

let freshness = (

let uu____10357 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____10357) with
| true -> begin
(

let uu____10360 = (

let uu____10361 = (

let uu____10367 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (

let uu____10373 = (varops.next_id ())
in ((vname), (uu____10367), (FStar_SMTEncoding_Term.Term_sort), (uu____10373))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____10361))
in (

let uu____10375 = (

let uu____10377 = (pretype_axiom vapp vars)
in (uu____10377)::[])
in (uu____10360)::uu____10375))
end
| uu____10378 -> begin
[]
end))
in (

let g = (

let uu____10381 = (

let uu____10383 = (

let uu____10385 = (

let uu____10387 = (

let uu____10389 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____10389)
in (FStar_List.append freshness uu____10387))
in (FStar_List.append decls3 uu____10385))
in (FStar_List.append decls2 uu____10383))
in (FStar_List.append decls1 uu____10381))
in ((g), (env)))))
end))
end))))
end))
end))))
end))
end)))
end))
end))))


let declare_top_level_let : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  ((Prims.string * FStar_SMTEncoding_Term.term Prims.option) * FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env x t t_norm -> (

let uu____10411 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10411) with
| None -> begin
(

let uu____10434 = (encode_free_var env x t t_norm [])
in (match (uu____10434) with
| (decls, env) -> begin
(

let uu____10449 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10449) with
| (n, x', uu____10468) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, uu____10480) -> begin
((((n), (x))), ([]), (env))
end)))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let uu____10513 = (encode_free_var env lid t tt quals)
in (match (uu____10513) with
| (decls, env) -> begin
(

let uu____10524 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____10524) with
| true -> begin
(

let uu____10528 = (

let uu____10530 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls uu____10530))
in ((uu____10528), (env)))
end
| uu____10533 -> begin
((decls), (env))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____10558 lb -> (match (uu____10558) with
| (decls, env) -> begin
(

let uu____10570 = (

let uu____10574 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env uu____10574 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____10570) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____10598 quals -> (match (uu____10598) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____10647 = (FStar_Util.first_N nbinders formals)
in (match (uu____10647) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun uu____10687 uu____10688 -> (match (((uu____10687), (uu____10688))) with
| ((formal, uu____10698), (binder, uu____10700)) -> begin
(

let uu____10705 = (

let uu____10710 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____10710)))
in FStar_Syntax_Syntax.NT (uu____10705))
end)) formals binders)
in (

let extra_formals = (

let uu____10715 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____10729 -> (match (uu____10729) with
| (x, i) -> begin
(

let uu____10736 = (

let uu___151_10737 = x
in (

let uu____10738 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___151_10737.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___151_10737.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____10738}))
in ((uu____10736), (i)))
end))))
in (FStar_All.pipe_right uu____10715 FStar_Syntax_Util.name_binders))
in (

let body = (

let uu____10750 = (

let uu____10752 = (

let uu____10753 = (FStar_Syntax_Subst.subst subst t)
in uu____10753.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _0_35 -> Some (_0_35)) uu____10752))
in (

let uu____10757 = (

let uu____10758 = (FStar_Syntax_Subst.compress body)
in (

let uu____10759 = (

let uu____10760 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd uu____10760))
in (FStar_Syntax_Syntax.extend_app_n uu____10758 uu____10759)))
in (uu____10757 uu____10750 body.FStar_Syntax_Syntax.pos)))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (

let uu____10848 = (

let uu____10849 = (FStar_Syntax_Util.unascribe e)
in uu____10849.FStar_Syntax_Syntax.n)
in (match (uu____10848) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let uu____10891 = (FStar_Syntax_Subst.open_term' binders body)
in (match (uu____10891) with
| (binders, body, opening) -> begin
(

let uu____10912 = (

let uu____10913 = (FStar_Syntax_Subst.compress t_norm)
in uu____10913.FStar_Syntax_Syntax.n)
in (match (uu____10912) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____10942 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____10942) with
| (formals, c) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (FStar_Syntax_Util.comp_result c)
in (

let uu____10972 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c))
in (match (uu____10972) with
| true -> begin
(

let lopt = (subst_lcomp_opt opening lopt)
in (

let uu____11002 = (FStar_Util.first_N nformals binders)
in (match (uu____11002) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun uu____11050 uu____11051 -> (match (((uu____11050), (uu____11051))) with
| ((b, uu____11061), (x, uu____11063)) -> begin
(

let uu____11068 = (

let uu____11073 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (uu____11073)))
in FStar_Syntax_Syntax.NT (uu____11068))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))), (false))))
end)))
end
| uu____11095 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____11115 = (eta_expand binders formals body tres)
in (match (uu____11115) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end))
end
| uu____11167 -> begin
((((binders), (body), (formals), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____11177) -> begin
(

let uu____11182 = (

let uu____11195 = (aux norm x.FStar_Syntax_Syntax.sort)
in (Prims.fst uu____11195))
in ((uu____11182), (true)))
end
| uu____11234 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| uu____11236 -> begin
(

let uu____11237 = (

let uu____11238 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11239 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____11238 uu____11239)))
in (failwith uu____11237))
end))
end))
end
| uu____11254 -> begin
(

let uu____11255 = (

let uu____11256 = (FStar_Syntax_Subst.compress t_norm)
in uu____11256.FStar_Syntax_Syntax.n)
in (match (uu____11255) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____11285 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____11285) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let uu____11307 = (eta_expand [] formals e tres)
in (match (uu____11307) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end)))
end))
end
| uu____11361 -> begin
(((([]), (e), ([]), (t_norm))), (false))
end))
end)))
in (aux false t_norm)))
in try
(match (()) with
| () -> begin
(

let uu____11389 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp))))
in (match (uu____11389) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____11395 -> begin
(

let uu____11396 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____11437 lb -> (match (uu____11437) with
| (toks, typs, decls, env) -> begin
((

let uu____11488 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____11488) with
| true -> begin
(Prims.raise Let_rec_unencodeable)
end
| uu____11489 -> begin
()
end));
(

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____11491 = (

let uu____11499 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env uu____11499 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____11491) with
| (tok, decl, env) -> begin
(

let uu____11524 = (

let uu____11531 = (

let uu____11537 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((uu____11537), (tok)))
in (uu____11531)::toks)
in ((uu____11524), ((t_norm)::typs), ((decl)::decls), (env)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____11396) with
| (toks, typs, decls, env) -> begin
(

let toks = (FStar_List.rev toks)
in (

let decls = (FStar_All.pipe_right (FStar_List.rev decls) FStar_List.flatten)
in (

let typs = (FStar_List.rev typs)
in (

let mk_app = (fun curry f ftok vars -> (match (vars) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____11639 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| Some (ftok) -> begin
(mk_Apply ftok vars)
end
| None -> begin
(

let uu____11644 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____11644 vars))
end)
end
| uu____11645 -> begin
(

let uu____11646 = (

let uu____11650 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____11650)))
in (FStar_SMTEncoding_Util.mkApp uu____11646))
end)
end))
in (

let uu____11655 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___123_11657 -> (match (uu___123_11657) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____11658 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (

let uu____11661 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation uu____11661))))))
in (match (uu____11655) with
| true -> begin
((decls), (env))
end
| uu____11666 -> begin
(match ((not (is_rec))) with
| true -> begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = uu____11681; FStar_Syntax_Syntax.lbunivs = uu____11682; FStar_Syntax_Syntax.lbtyp = uu____11683; FStar_Syntax_Syntax.lbeff = uu____11684; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____11726 = (destruct_bound_function flid t_norm e)
in (match (uu____11726) with
| ((binders, body, uu____11746, uu____11747), curry) -> begin
(

let uu____11777 = (encode_binders None binders env)
in (match (uu____11777) with
| (vars, guards, env', binder_decls, uu____11793) -> begin
(

let app = (mk_app curry f ftok vars)
in (

let uu____11801 = (

let uu____11806 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____11806) with
| true -> begin
(

let uu____11812 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____11813 = (encode_formula body env')
in ((uu____11812), (uu____11813))))
end
| uu____11818 -> begin
(

let uu____11819 = (encode_term body env')
in ((app), (uu____11819)))
end))
in (match (uu____11801) with
| (app, (body, decls2)) -> begin
(

let eqn = (

let uu____11833 = (

let uu____11838 = (

let uu____11839 = (

let uu____11845 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (uu____11845)))
in (FStar_SMTEncoding_Util.mkForall uu____11839))
in (

let uu____11851 = (

let uu____11853 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (uu____11853))
in ((uu____11838), (uu____11851), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (uu____11833))
in (

let uu____11856 = (

let uu____11858 = (

let uu____11860 = (

let uu____11862 = (

let uu____11864 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) uu____11864))
in (FStar_List.append decls2 uu____11862))
in (FStar_List.append binder_decls uu____11860))
in (FStar_List.append decls uu____11858))
in ((uu____11856), (env))))
end)))
end))
end))))
end
| uu____11867 -> begin
(failwith "Impossible")
end)
end
| uu____11882 -> begin
(

let fuel = (

let uu____11886 = (varops.fresh "fuel")
in ((uu____11886), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env
in (

let uu____11889 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun uu____11928 uu____11929 -> (match (((uu____11928), (uu____11929))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (

let uu____12011 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____12011))
in (

let gtok = (

let uu____12013 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____12013))
in (

let env = (

let uu____12015 = (

let uu____12017 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_36 -> Some (_0_36)) uu____12017))
in (push_free_var env flid gtok uu____12015))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (uu____11889) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 uu____12101 t_norm uu____12103 -> (match (((uu____12101), (uu____12103))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = uu____12126; FStar_Syntax_Syntax.lbunivs = uu____12127; FStar_Syntax_Syntax.lbtyp = uu____12128; FStar_Syntax_Syntax.lbeff = uu____12129; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let uu____12146 = (destruct_bound_function flid t_norm e)
in (match (uu____12146) with
| ((binders, body, formals, tres), curry) -> begin
((match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____12200 -> begin
()
end);
(

let uu____12201 = (encode_binders None binders env)
in (match (uu____12201) with
| (vars, guards, env', binder_decls, uu____12219) -> begin
(

let decl_g = (

let uu____12227 = (

let uu____12233 = (

let uu____12235 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____12235)
in ((g), (uu____12233), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____12227))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____12250 = (

let uu____12254 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____12254)))
in (FStar_SMTEncoding_Util.mkApp uu____12250))
in (

let gsapp = (

let uu____12260 = (

let uu____12264 = (

let uu____12266 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____12266)::vars_tm)
in ((g), (uu____12264)))
in (FStar_SMTEncoding_Util.mkApp uu____12260))
in (

let gmax = (

let uu____12270 = (

let uu____12274 = (

let uu____12276 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____12276)::vars_tm)
in ((g), (uu____12274)))
in (FStar_SMTEncoding_Util.mkApp uu____12270))
in (

let uu____12279 = (encode_term body env')
in (match (uu____12279) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____12290 = (

let uu____12295 = (

let uu____12296 = (

let uu____12304 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____12304)))
in (FStar_SMTEncoding_Util.mkForall' uu____12296))
in (

let uu____12315 = (

let uu____12317 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (uu____12317))
in ((uu____12295), (uu____12315), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (uu____12290))
in (

let eqn_f = (

let uu____12321 = (

let uu____12326 = (

let uu____12327 = (

let uu____12333 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____12333)))
in (FStar_SMTEncoding_Util.mkForall uu____12327))
in ((uu____12326), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12321))
in (

let eqn_g' = (

let uu____12342 = (

let uu____12347 = (

let uu____12348 = (

let uu____12354 = (

let uu____12355 = (

let uu____12358 = (

let uu____12359 = (

let uu____12363 = (

let uu____12365 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____12365)::vars_tm)
in ((g), (uu____12363)))
in (FStar_SMTEncoding_Util.mkApp uu____12359))
in ((gsapp), (uu____12358)))
in (FStar_SMTEncoding_Util.mkEq uu____12355))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____12354)))
in (FStar_SMTEncoding_Util.mkForall uu____12348))
in ((uu____12347), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12342))
in (

let uu____12378 = (

let uu____12383 = (encode_binders None formals env0)
in (match (uu____12383) with
| (vars, v_guards, env, binder_decls, uu____12400) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (

let uu____12415 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____12415 ((fuel)::vars)))
in (

let uu____12418 = (

let uu____12423 = (

let uu____12424 = (

let uu____12430 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (uu____12430)))
in (FStar_SMTEncoding_Util.mkForall uu____12424))
in ((uu____12423), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (uu____12418)))
in (

let uu____12442 = (

let uu____12446 = (encode_term_pred None tres env gapp)
in (match (uu____12446) with
| (g_typing, d3) -> begin
(

let uu____12454 = (

let uu____12456 = (

let uu____12457 = (

let uu____12462 = (

let uu____12463 = (

let uu____12469 = (

let uu____12470 = (

let uu____12473 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____12473), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____12470))
in ((((gapp)::[])::[]), ((fuel)::vars), (uu____12469)))
in (FStar_SMTEncoding_Util.mkForall uu____12463))
in ((uu____12462), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12457))
in (uu____12456)::[])
in ((d3), (uu____12454)))
end))
in (match (uu____12442) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____12378) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end));
)
end))
end))
in (

let uu____12509 = (

let uu____12516 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun uu____12548 uu____12549 -> (match (((uu____12548), (uu____12549))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let uu____12625 = (encode_one_binding env0 gtok ty bs)
in (match (uu____12625) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) uu____12516))
in (match (uu____12509) with
| (decls, eqns, env0) -> begin
(

let uu____12665 = (

let uu____12670 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right uu____12670 (FStar_List.partition (fun uu___124_12680 -> (match (uu___124_12680) with
| FStar_SMTEncoding_Term.DeclFun (uu____12681) -> begin
true
end
| uu____12687 -> begin
false
end)))))
in (match (uu____12665) with
| (prefix_decls, rest) -> begin
(

let eqns = (FStar_List.rev eqns)
in (((FStar_List.append prefix_decls (FStar_List.append rest eqns))), (env0)))
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

let uu____12705 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____12705 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> ((

let uu____12738 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12738) with
| true -> begin
(

let uu____12739 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") uu____12739))
end
| uu____12740 -> begin
()
end));
(

let nm = (match ((FStar_Syntax_Util.lid_of_sigelt se)) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end)
in (

let uu____12743 = (encode_sigelt' env se)
in (match (uu____12743) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(

let uu____12752 = (

let uu____12754 = (

let uu____12755 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12755))
in (uu____12754)::[])
in ((uu____12752), (e)))
end
| uu____12757 -> begin
(

let uu____12758 = (

let uu____12760 = (

let uu____12762 = (

let uu____12763 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12763))
in (uu____12762)::g)
in (

let uu____12764 = (

let uu____12766 = (

let uu____12767 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12767))
in (uu____12766)::[])
in (FStar_List.append uu____12760 uu____12764)))
in ((uu____12758), (e)))
end)
end)));
))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____12779) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, uu____12790) -> begin
(

let uu____12791 = (

let uu____12792 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____12792 Prims.op_Negation))
in (match (uu____12791) with
| true -> begin
(([]), (env))
end
| uu____12797 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____12812 -> begin
(

let uu____12813 = (

let uu____12816 = (

let uu____12817 = (

let uu____12832 = (FStar_All.pipe_left (fun _0_37 -> Some (_0_37)) (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (uu____12832)))
in FStar_Syntax_Syntax.Tm_abs (uu____12817))
in (FStar_Syntax_Syntax.mk uu____12816))
in (uu____12813 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env a -> (

let uu____12885 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (uu____12885) with
| (aname, atok, env) -> begin
(

let uu____12895 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____12895) with
| (formals, uu____12905) -> begin
(

let uu____12912 = (

let uu____12915 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____12915 env))
in (match (uu____12912) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____12923 = (

let uu____12924 = (

let uu____12930 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____12938 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____12930), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____12924))
in (uu____12923)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let uu____12945 = (

let uu____12952 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____12972 -> (match (uu____12972) with
| (bv, uu____12980) -> begin
(

let uu____12981 = (gen_term_var env bv)
in (match (uu____12981) with
| (xxsym, xx, uu____12991) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right uu____12952 FStar_List.split))
in (match (uu____12945) with
| (xs_sorts, xs) -> begin
(

let app = (

let uu____13021 = (

let uu____13025 = (

let uu____13027 = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (uu____13027)::[])
in (("Reify"), (uu____13025)))
in (FStar_SMTEncoding_Util.mkApp uu____13021))
in (

let a_eq = (

let uu____13031 = (

let uu____13036 = (

let uu____13037 = (

let uu____13043 = (

let uu____13044 = (

let uu____13047 = (mk_Apply tm xs_sorts)
in ((app), (uu____13047)))
in (FStar_SMTEncoding_Util.mkEq uu____13044))
in ((((app)::[])::[]), (xs_sorts), (uu____13043)))
in (FStar_SMTEncoding_Util.mkForall uu____13037))
in ((uu____13036), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (uu____13031))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____13060 = (

let uu____13065 = (

let uu____13066 = (

let uu____13072 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____13072)))
in (FStar_SMTEncoding_Util.mkForall uu____13066))
in ((uu____13065), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (uu____13060))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____13083 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____13083) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13099, uu____13100, uu____13101, uu____13102) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let uu____13105 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____13105) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13116, t, quals, uu____13119) -> begin
(

let will_encode_definition = (

let uu____13123 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___125_13125 -> (match (uu___125_13125) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| uu____13128 -> begin
false
end))))
in (not (uu____13123)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____13132 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____13134 = (encode_top_level_val env fv t quals)
in (match (uu____13134) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____13146 = (

let uu____13148 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls uu____13148))
in ((uu____13146), (env)))))
end)))
end))
end
| FStar_Syntax_Syntax.Sig_assume (l, f, uu____13153, uu____13154) -> begin
(

let uu____13157 = (encode_formula f env)
in (match (uu____13157) with
| (f, decls) -> begin
(

let g = (

let uu____13166 = (

let uu____13167 = (

let uu____13172 = (

let uu____13174 = (

let uu____13175 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____13175))
in Some (uu____13174))
in (

let uu____13176 = (

let uu____13178 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (uu____13178))
in ((f), (uu____13172), (uu____13176))))
in FStar_SMTEncoding_Term.Assume (uu____13167))
in (uu____13166)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, uu____13184, quals, uu____13186) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let uu____13194 = (FStar_Util.fold_map (fun env lb -> (

let lid = (

let uu____13201 = (

let uu____13206 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____13206.FStar_Syntax_Syntax.fv_name)
in uu____13201.FStar_Syntax_Syntax.v)
in (

let uu____13210 = (

let uu____13211 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____13211))
in (match (uu____13210) with
| true -> begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let uu____13230 = (encode_sigelt' env val_decl)
in (match (uu____13230) with
| (decls, env) -> begin
((env), (decls))
end)))
end
| uu____13237 -> begin
((env), ([]))
end)))) env (Prims.snd lbs))
in (match (uu____13194) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____13247, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = uu____13249; FStar_Syntax_Syntax.lbtyp = uu____13250; FStar_Syntax_Syntax.lbeff = uu____13251; FStar_Syntax_Syntax.lbdef = uu____13252})::[]), uu____13253, uu____13254, uu____13255, uu____13256) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let uu____13272 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____13272) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid_b2t_x = (

let uu____13290 = (

let uu____13294 = (

let uu____13296 = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (uu____13296)::[])
in (("Valid"), (uu____13294)))
in (FStar_SMTEncoding_Util.mkApp uu____13290))
in (

let decls = (

let uu____13301 = (

let uu____13303 = (

let uu____13304 = (

let uu____13309 = (

let uu____13310 = (

let uu____13316 = (

let uu____13317 = (

let uu____13320 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (uu____13320)))
in (FStar_SMTEncoding_Util.mkEq uu____13317))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (uu____13316)))
in (FStar_SMTEncoding_Util.mkForall uu____13310))
in ((uu____13309), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (uu____13304))
in (uu____13303)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::uu____13301)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____13338, uu____13339, uu____13340, quals, uu____13342) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___126_13350 -> (match (uu___126_13350) with
| FStar_Syntax_Syntax.Discriminator (uu____13351) -> begin
true
end
| uu____13352 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____13354, uu____13355, lids, quals, uu____13358) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____13367 = (

let uu____13368 = (FStar_List.hd l.FStar_Ident.ns)
in uu____13368.FStar_Ident.idText)
in (uu____13367 = "Prims"))))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___127_13370 -> (match (uu___127_13370) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____13371 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____13374, uu____13375, quals, uu____13377) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___128_13389 -> (match (uu___128_13389) with
| FStar_Syntax_Syntax.Projector (uu____13390) -> begin
true
end
| uu____13393 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____13400 = (try_lookup_free_var env l)
in (match (uu____13400) with
| Some (uu____13404) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____13412, uu____13413, quals, uu____13415) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let uu____13427 = (

let uu____13428 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in uu____13428.FStar_Syntax_Syntax.n)
in (match (uu____13427) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____13435) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let uu____13492 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____13492) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let uu___154_13509 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___154_13509.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___154_13509.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___154_13509.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___154_13509.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___154_13509.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___154_13509.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___154_13509.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___154_13509.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___154_13509.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___154_13509.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___154_13509.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___154_13509.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___154_13509.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___154_13509.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___154_13509.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___154_13509.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___154_13509.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___154_13509.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___154_13509.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___154_13509.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___154_13509.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___154_13509.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___154_13509.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (

let uu____13510 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals uu____13510)))
end))
in (

let lb = (

let uu___155_13514 = lb
in {FStar_Syntax_Syntax.lbname = uu___155_13514.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___155_13514.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = uu___155_13514.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in ((

let uu____13516 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____13517 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____13518 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print3 "%s: Reified %s\nto %s\n" uu____13516 uu____13517 uu____13518))));
(encode_top_level_let env ((false), ((lb)::[])) quals);
))))))
end
| uu____13520 -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____13524, uu____13525, quals, uu____13527) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____13541, uu____13542, uu____13543) -> begin
(

let uu____13550 = (encode_signature env ses)
in (match (uu____13550) with
| (g, env) -> begin
(

let uu____13560 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___129_13570 -> (match (uu___129_13570) with
| FStar_SMTEncoding_Term.Assume (uu____13571, Some ("inversion axiom"), uu____13572) -> begin
false
end
| uu____13576 -> begin
true
end))))
in (match (uu____13560) with
| (g', inversions) -> begin
(

let uu____13585 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___130_13595 -> (match (uu___130_13595) with
| FStar_SMTEncoding_Term.DeclFun (uu____13596) -> begin
true
end
| uu____13602 -> begin
false
end))))
in (match (uu____13585) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____13613, tps, k, uu____13616, datas, quals, uu____13619) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___131_13628 -> (match (uu___131_13628) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| uu____13629 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____13652 = c
in (match (uu____13652) with
| (name, args, uu____13664, uu____13665, uu____13666) -> begin
(

let uu____13673 = (

let uu____13674 = (

let uu____13680 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (uu____13680), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____13674))
in (uu____13673)::[])
end))
end
| uu____13690 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____13705 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____13708 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____13708 FStar_Option.isNone)))))
in (match (uu____13705) with
| true -> begin
[]
end
| uu____13718 -> begin
(

let uu____13719 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13719) with
| (xxsym, xx) -> begin
(

let uu____13725 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____13736 l -> (match (uu____13736) with
| (out, decls) -> begin
(

let uu____13748 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____13748) with
| (uu____13754, data_t) -> begin
(

let uu____13756 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____13756) with
| (args, res) -> begin
(

let indices = (

let uu____13785 = (

let uu____13786 = (FStar_Syntax_Subst.compress res)
in uu____13786.FStar_Syntax_Syntax.n)
in (match (uu____13785) with
| FStar_Syntax_Syntax.Tm_app (uu____13794, indices) -> begin
indices
end
| uu____13810 -> begin
[]
end))
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env uu____13822 -> (match (uu____13822) with
| (x, uu____13826) -> begin
(

let uu____13827 = (

let uu____13828 = (

let uu____13832 = (mk_term_projector_name l x)
in ((uu____13832), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____13828))
in (push_term_var env x uu____13827))
end)) env))
in (

let uu____13834 = (encode_args indices env)
in (match (uu____13834) with
| (indices, decls') -> begin
((match (((FStar_List.length indices) <> (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____13852 -> begin
()
end);
(

let eqs = (

let uu____13854 = (FStar_List.map2 (fun v a -> (

let uu____13862 = (

let uu____13865 = (FStar_SMTEncoding_Util.mkFreeV v)
in ((uu____13865), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____13862))) vars indices)
in (FStar_All.pipe_right uu____13854 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____13867 = (

let uu____13868 = (

let uu____13871 = (

let uu____13872 = (

let uu____13875 = (mk_data_tester env l xx)
in ((uu____13875), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____13872))
in ((out), (uu____13871)))
in (FStar_SMTEncoding_Util.mkOr uu____13868))
in ((uu____13867), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____13725) with
| (data_ax, decls) -> begin
(

let uu____13883 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____13883) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____13894 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____13894 xx tapp))
end
| uu____13896 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____13897 = (

let uu____13902 = (

let uu____13903 = (

let uu____13909 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____13917 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____13909), (uu____13917))))
in (FStar_SMTEncoding_Util.mkForall uu____13903))
in (

let uu____13925 = (

let uu____13927 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (uu____13927))
in ((uu____13902), (Some ("inversion axiom")), (uu____13925))))
in FStar_SMTEncoding_Term.Assume (uu____13897)))
in (

let pattern_guarded_inversion = (

let uu____13932 = ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1")))
in (match (uu____13932) with
| true -> begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (

let uu____13940 = (

let uu____13941 = (

let uu____13946 = (

let uu____13947 = (

let uu____13953 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____13961 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (uu____13953), (uu____13961))))
in (FStar_SMTEncoding_Util.mkForall uu____13947))
in (

let uu____13969 = (

let uu____13971 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (uu____13971))
in ((uu____13946), (Some ("inversion axiom")), (uu____13969))))
in FStar_SMTEncoding_Term.Assume (uu____13941))
in (uu____13940)::[])))
end
| uu____13974 -> begin
[]
end))
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)))
in (

let uu____13975 = (

let uu____13983 = (

let uu____13984 = (FStar_Syntax_Subst.compress k)
in uu____13984.FStar_Syntax_Syntax.n)
in (match (uu____13983) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____14013 -> begin
((tps), (k))
end))
in (match (uu____13975) with
| (formals, res) -> begin
(

let uu____14028 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____14028) with
| (formals, res) -> begin
(

let uu____14035 = (encode_binders None formals env)
in (match (uu____14035) with
| (vars, guards, env', binder_decls, uu____14050) -> begin
(

let uu____14057 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____14057) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____14070 = (

let uu____14074 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____14074)))
in (FStar_SMTEncoding_Util.mkApp uu____14070))
in (

let uu____14079 = (

let tname_decl = (

let uu____14085 = (

let uu____14094 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____14106 -> (match (uu____14106) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (

let uu____14113 = (varops.next_id ())
in ((tname), (uu____14094), (FStar_SMTEncoding_Term.Term_sort), (uu____14113), (false))))
in (constructor_or_logic_type_decl uu____14085))
in (

let uu____14117 = (match (vars) with
| [] -> begin
(

let uu____14124 = (

let uu____14125 = (

let uu____14127 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_38 -> Some (_0_38)) uu____14127))
in (push_free_var env t tname uu____14125))
in (([]), (uu____14124)))
end
| uu____14131 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (

let uu____14137 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____14137))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____14146 = (

let uu____14151 = (

let uu____14152 = (

let uu____14160 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (uu____14160)))
in (FStar_SMTEncoding_Util.mkForall' uu____14152))
in ((uu____14151), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14146))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (uu____14117) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (uu____14079) with
| (decls, env) -> begin
(

let kindingAx = (

let uu____14184 = (encode_term_pred None res env' tapp)
in (match (uu____14184) with
| (k, decls) -> begin
(

let karr = (match (((FStar_List.length formals) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____14198 = (

let uu____14199 = (

let uu____14204 = (

let uu____14205 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____14205))
in ((uu____14204), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14199))
in (uu____14198)::[])
end
| uu____14208 -> begin
[]
end)
in (

let uu____14209 = (

let uu____14211 = (

let uu____14213 = (

let uu____14214 = (

let uu____14219 = (

let uu____14220 = (

let uu____14226 = (FStar_SMTEncoding_Util.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (uu____14226)))
in (FStar_SMTEncoding_Util.mkForall uu____14220))
in ((uu____14219), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14214))
in (uu____14213)::[])
in (FStar_List.append karr uu____14211))
in (FStar_List.append decls uu____14209)))
end))
in (

let aux = (

let uu____14236 = (

let uu____14238 = (inversion_axioms tapp vars)
in (

let uu____14240 = (

let uu____14242 = (pretype_axiom tapp vars)
in (uu____14242)::[])
in (FStar_List.append uu____14238 uu____14240)))
in (FStar_List.append kindingAx uu____14236))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14247, uu____14248, uu____14249, uu____14250, uu____14251, uu____14252, uu____14253) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14260, t, uu____14262, n_tps, quals, uu____14265, drange) -> begin
(

let uu____14271 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____14271) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____14282 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____14282) with
| (formals, t_res) -> begin
(

let uu____14304 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____14304) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____14313 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____14313) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (

let uu____14346 = (mk_term_projector_name d x)
in ((uu____14346), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (

let uu____14348 = (

let uu____14357 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (uu____14357), (true)))
in (FStar_All.pipe_right uu____14348 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____14377 = (encode_term_pred None t env ddtok_tm)
in (match (uu____14377) with
| (tok_typing, decls3) -> begin
(

let uu____14384 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____14384) with
| (vars', guards', env'', decls_formals, uu____14399) -> begin
(

let uu____14406 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (uu____14406) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____14425 -> begin
(

let uu____14429 = (

let uu____14430 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____14430))
in (uu____14429)::[])
end)
in (

let encode_elim = (fun uu____14437 -> (

let uu____14438 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____14438) with
| (head, args) -> begin
(

let uu____14467 = (

let uu____14468 = (FStar_Syntax_Subst.compress head)
in uu____14468.FStar_Syntax_Syntax.n)
in (match (uu____14467) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____14486 = (encode_args args env')
in (match (uu____14486) with
| (encoded_args, arg_decls) -> begin
(

let uu____14497 = (FStar_List.fold_left (fun uu____14508 arg -> (match (uu____14508) with
| (env, arg_vars, eqns) -> begin
(

let uu____14527 = (

let uu____14531 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env uu____14531))
in (match (uu____14527) with
| (uu____14537, xv, env) -> begin
(

let uu____14540 = (

let uu____14542 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____14542)::eqns)
in ((env), ((xv)::arg_vars), (uu____14540)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (uu____14497) with
| (uu____14550, arg_vars, eqns) -> begin
(

let arg_vars = (FStar_List.rev arg_vars)
in (

let ty = (FStar_SMTEncoding_Util.mkApp ((encoded_head), (arg_vars)))
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let ty_pred = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (s_fuel_tm)) dapp ty)
in (

let arg_binders = (FStar_List.map FStar_SMTEncoding_Term.fv_of_term arg_vars)
in (

let typing_inversion = (

let uu____14571 = (

let uu____14576 = (

let uu____14577 = (

let uu____14583 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14589 = (

let uu____14590 = (

let uu____14593 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (uu____14593)))
in (FStar_SMTEncoding_Util.mkImp uu____14590))
in ((((ty_pred)::[])::[]), (uu____14583), (uu____14589))))
in (FStar_SMTEncoding_Util.mkForall uu____14577))
in ((uu____14576), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (uu____14571))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____14607 = (varops.fresh "x")
in ((uu____14607), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____14609 = (

let uu____14614 = (

let uu____14615 = (

let uu____14621 = (

let uu____14624 = (

let uu____14626 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in (uu____14626)::[])
in (uu____14624)::[])
in (

let uu____14629 = (

let uu____14630 = (

let uu____14633 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____14634 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in ((uu____14633), (uu____14634))))
in (FStar_SMTEncoding_Util.mkImp uu____14630))
in ((uu____14621), ((x)::[]), (uu____14629))))
in (FStar_SMTEncoding_Util.mkForall uu____14615))
in (

let uu____14644 = (

let uu____14646 = (varops.mk_unique "lextop")
in Some (uu____14646))
in ((uu____14614), (Some ("lextop is top")), (uu____14644))))
in FStar_SMTEncoding_Term.Assume (uu____14609))))
end
| uu____14649 -> begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(

let uu____14660 = (

let uu____14661 = (FStar_SMTEncoding_Util.mkFreeV v)
in (FStar_SMTEncoding_Util.mk_Precedes uu____14661 dapp))
in (uu____14660)::[])
end
| uu____14662 -> begin
(failwith "unexpected sort")
end))))
in (

let uu____14664 = (

let uu____14669 = (

let uu____14670 = (

let uu____14676 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14682 = (

let uu____14683 = (

let uu____14686 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____14686)))
in (FStar_SMTEncoding_Util.mkImp uu____14683))
in ((((ty_pred)::[])::[]), (uu____14676), (uu____14682))))
in (FStar_SMTEncoding_Util.mkForall uu____14670))
in ((uu____14669), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (uu____14664)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| uu____14697 -> begin
((

let uu____14699 = (

let uu____14700 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____14701 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____14700 uu____14701)))
in (FStar_Errors.warn drange uu____14699));
(([]), ([]));
)
end))
end)))
in (

let uu____14704 = (encode_elim ())
in (match (uu____14704) with
| (decls2, elim) -> begin
(

let g = (

let uu____14716 = (

let uu____14718 = (

let uu____14720 = (

let uu____14722 = (

let uu____14724 = (

let uu____14725 = (

let uu____14731 = (

let uu____14733 = (

let uu____14734 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____14734))
in Some (uu____14733))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____14731)))
in FStar_SMTEncoding_Term.DeclFun (uu____14725))
in (uu____14724)::[])
in (

let uu____14737 = (

let uu____14739 = (

let uu____14741 = (

let uu____14743 = (

let uu____14745 = (

let uu____14747 = (

let uu____14749 = (

let uu____14750 = (

let uu____14755 = (

let uu____14756 = (

let uu____14762 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____14762)))
in (FStar_SMTEncoding_Util.mkForall uu____14756))
in ((uu____14755), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (uu____14750))
in (

let uu____14770 = (

let uu____14772 = (

let uu____14773 = (

let uu____14778 = (

let uu____14779 = (

let uu____14785 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____14791 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____14785), (uu____14791))))
in (FStar_SMTEncoding_Util.mkForall uu____14779))
in ((uu____14778), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (uu____14773))
in (uu____14772)::[])
in (uu____14749)::uu____14770))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::uu____14747)
in (FStar_List.append uu____14745 elim))
in (FStar_List.append decls_pred uu____14743))
in (FStar_List.append decls_formals uu____14741))
in (FStar_List.append proxy_fresh uu____14739))
in (FStar_List.append uu____14722 uu____14737)))
in (FStar_List.append decls3 uu____14720))
in (FStar_List.append decls2 uu____14718))
in (FStar_List.append binder_decls uu____14716))
in (((FStar_List.append datacons g)), (env)))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end))
end)))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____14814 se -> (match (uu____14814) with
| (g, env) -> begin
(

let uu____14826 = (encode_sigelt env se)
in (match (uu____14826) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____14862 -> (match (uu____14862) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____14880) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____14885 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____14885) with
| true -> begin
(

let uu____14886 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14887 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14888 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____14886 uu____14887 uu____14888))))
end
| uu____14889 -> begin
()
end));
(

let uu____14890 = (encode_term t1 env)
in (match (uu____14890) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____14900 = (

let uu____14904 = (

let uu____14905 = (

let uu____14906 = (FStar_Util.digest_of_string t_hash)
in (

let uu____14907 = (

let uu____14908 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____14908))
in (Prims.strcat uu____14906 uu____14907)))
in (Prims.strcat "x_" uu____14905))
in (new_term_constant_from_string env x uu____14904))
in (match (uu____14900) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = (

let uu____14919 = (FStar_Options.log_queries ())
in (match (uu____14919) with
| true -> begin
(

let uu____14921 = (

let uu____14922 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14923 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14924 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____14922 uu____14923 uu____14924))))
in Some (uu____14921))
end
| uu____14925 -> begin
None
end))
in (

let ax = (

let a_name = Some ((Prims.strcat "binder_" xxsym))
in FStar_SMTEncoding_Term.Assume (((t), (a_name), (a_name))))
in (

let g = (FStar_List.append ((FStar_SMTEncoding_Term.DeclFun (((xxsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (caption))))::[]) (FStar_List.append decls' ((ax)::[])))
in (((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))))))
end)))
end));
))
end
| FStar_TypeChecker_Env.Binding_lid (x, (uu____14937, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____14946 = (encode_free_var env fv t t_norm [])
in (match (uu____14946) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let uu____14965 = (encode_sigelt env se)
in (match (uu____14965) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____14975 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____14975) with
| (uu____14987, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun uu____15032 -> (match (uu____15032) with
| (l, uu____15039, uu____15040) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____15061 -> (match (uu____15061) with
| (l, uu____15069, uu____15070) -> begin
(

let uu____15075 = (FStar_All.pipe_left (fun _0_39 -> FStar_SMTEncoding_Term.Echo (_0_39)) (Prims.fst l))
in (

let uu____15076 = (

let uu____15078 = (

let uu____15079 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____15079))
in (uu____15078)::[])
in (uu____15075)::uu____15076))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____15090 = (

let uu____15092 = (

let uu____15093 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____15093; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (uu____15092)::[])
in (FStar_ST.write last_env uu____15090)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (

let uu____15111 = (FStar_ST.read last_env)
in (match (uu____15111) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____15117 -> begin
(

let uu___156_15119 = e
in {bindings = uu___156_15119.bindings; depth = uu___156_15119.depth; tcenv = tcenv; warn = uu___156_15119.warn; cache = uu___156_15119.cache; nolabels = uu___156_15119.nolabels; use_zfuel_name = uu___156_15119.use_zfuel_name; encode_non_total_function_typ = uu___156_15119.encode_non_total_function_typ})
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____15123 = (FStar_ST.read last_env)
in (match (uu____15123) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____15128)::tl -> begin
(FStar_ST.write last_env ((env)::tl))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____15136 -> (

let uu____15137 = (FStar_ST.read last_env)
in (match (uu____15137) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd)::tl -> begin
(

let refs = (FStar_Util.smap_copy hd.cache)
in (

let top = (

let uu___157_15158 = hd
in {bindings = uu___157_15158.bindings; depth = uu___157_15158.depth; tcenv = uu___157_15158.tcenv; warn = uu___157_15158.warn; cache = refs; nolabels = uu___157_15158.nolabels; use_zfuel_name = uu___157_15158.use_zfuel_name; encode_non_total_function_typ = uu___157_15158.encode_non_total_function_typ})
in (FStar_ST.write last_env ((top)::(hd)::tl))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____15164 -> (

let uu____15165 = (FStar_ST.read last_env)
in (match (uu____15165) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____15170)::tl -> begin
(FStar_ST.write last_env tl)
end)))


let mark_env : Prims.unit  ->  Prims.unit = (fun uu____15178 -> (push_env ()))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15181 -> (pop_env ()))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15184 -> (

let uu____15185 = (FStar_ST.read last_env)
in (match (uu____15185) with
| (hd)::(uu____15191)::tl -> begin
(FStar_ST.write last_env ((hd)::tl))
end
| uu____15197 -> begin
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


let encode_sig : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun tcenv se -> (

let caption = (fun decls -> (

let uu____15242 = (FStar_Options.log_queries ())
in (match (uu____15242) with
| true -> begin
(

let uu____15244 = (

let uu____15245 = (

let uu____15246 = (

let uu____15247 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____15247 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____15246))
in FStar_SMTEncoding_Term.Caption (uu____15245))
in (uu____15244)::decls)
end
| uu____15252 -> begin
decls
end)))
in (

let env = (get_env tcenv)
in (

let uu____15254 = (encode_sigelt env se)
in (match (uu____15254) with
| (decls, env) -> begin
((set_env env);
(

let uu____15260 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____15260));
)
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____15269 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____15271 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15271) with
| true -> begin
(

let uu____15272 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____15272))
end
| uu____15275 -> begin
()
end));
(

let env = (get_env tcenv)
in (

let uu____15277 = (encode_signature (

let uu___158_15281 = env
in {bindings = uu___158_15281.bindings; depth = uu___158_15281.depth; tcenv = uu___158_15281.tcenv; warn = false; cache = uu___158_15281.cache; nolabels = uu___158_15281.nolabels; use_zfuel_name = uu___158_15281.use_zfuel_name; encode_non_total_function_typ = uu___158_15281.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____15277) with
| (decls, env) -> begin
(

let caption = (fun decls -> (

let uu____15293 = (FStar_Options.log_queries ())
in (match (uu____15293) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____15296 -> begin
decls
end)))
in ((set_env (

let uu___159_15298 = env
in {bindings = uu___159_15298.bindings; depth = uu___159_15298.depth; tcenv = uu___159_15298.tcenv; warn = true; cache = uu___159_15298.cache; nolabels = uu___159_15298.nolabels; use_zfuel_name = uu___159_15298.use_zfuel_name; encode_non_total_function_typ = uu___159_15298.encode_non_total_function_typ}));
(

let uu____15300 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15300) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____15301 -> begin
()
end));
(

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls));
))
end)));
)))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____15335 = (

let uu____15336 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____15336.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____15335));
(

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____15344 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____15365 = (aux rest)
in (match (uu____15365) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let uu____15381 = (

let uu____15383 = (FStar_Syntax_Syntax.mk_binder (

let uu___160_15384 = x
in {FStar_Syntax_Syntax.ppname = uu___160_15384.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___160_15384.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (uu____15383)::out)
in ((uu____15381), (rest))))
end))
end
| uu____15387 -> begin
(([]), (bindings))
end))
in (

let uu____15391 = (aux bindings)
in (match (uu____15391) with
| (closing, bindings) -> begin
(

let uu____15405 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((uu____15405), (bindings)))
end)))
in (match (uu____15344) with
| (q, bindings) -> begin
(

let uu____15418 = (

let uu____15421 = (FStar_List.filter (fun uu___132_15423 -> (match (uu___132_15423) with
| FStar_TypeChecker_Env.Binding_sig (uu____15424) -> begin
false
end
| uu____15428 -> begin
true
end)) bindings)
in (encode_env_bindings env uu____15421))
in (match (uu____15418) with
| (env_decls, env) -> begin
((

let uu____15439 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____15439) with
| true -> begin
(

let uu____15440 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____15440))
end
| uu____15441 -> begin
()
end));
(

let uu____15442 = (encode_formula q env)
in (match (uu____15442) with
| (phi, qdecls) -> begin
(

let uu____15454 = (

let uu____15457 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____15457 phi))
in (match (uu____15454) with
| (labels, phi) -> begin
(

let uu____15467 = (encode_labels labels)
in (match (uu____15467) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____15488 = (

let uu____15493 = (FStar_SMTEncoding_Util.mkNot phi)
in (

let uu____15494 = (

let uu____15496 = (varops.mk_unique "@query")
in Some (uu____15496))
in ((uu____15493), (Some ("query")), (uu____15494))))
in FStar_SMTEncoding_Term.Assume (uu____15488))
in (

let suffix = (

let uu____15501 = (

let uu____15503 = (

let uu____15505 = (FStar_Options.print_z3_statistics ())
in (match (uu____15505) with
| true -> begin
(FStar_SMTEncoding_Term.PrintStats)::[]
end
| uu____15507 -> begin
[]
end))
in (FStar_List.append uu____15503 ((FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in (FStar_List.append label_suffix uu____15501))
in ((query_prelude), (labels), (qry), (suffix)))))
end))
end))
end));
)
end))
end))));
))


let is_trivial : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun tcenv q -> (

let env = (get_env tcenv)
in ((FStar_SMTEncoding_Z3.push "query");
(

let uu____15518 = (encode_formula q env)
in (match (uu____15518) with
| (f, uu____15522) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____15524) -> begin
true
end
| uu____15527 -> begin
false
end);
)
end));
)))





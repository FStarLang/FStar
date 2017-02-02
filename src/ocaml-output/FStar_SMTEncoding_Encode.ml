
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
(match (args) with
| (x)::[] -> begin
(Prims.fst x)
end
| uu____3424 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____3430 -> begin
e0
end))
end))
end))
in (

let e = (match (args_e) with
| (uu____3432)::[] -> begin
e0
end
| uu____3445 -> begin
(

let uu____3451 = (

let uu____3454 = (

let uu____3455 = (

let uu____3465 = (FStar_List.tl args_e)
in ((e0), (uu____3465)))
in FStar_Syntax_Syntax.Tm_app (uu____3455))
in (FStar_Syntax_Syntax.mk uu____3454))
in (uu____3451 None t0.FStar_Syntax_Syntax.pos))
end)
in (encode_term e env)));
));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____3488)), ((arg, uu____3490))::[]) -> begin
(encode_term arg env)
end
| uu____3508 -> begin
(

let uu____3516 = (encode_args args_e env)
in (match (uu____3516) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____3549 = (encode_term head env)
in (match (uu____3549) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let uu____3588 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____3588) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun uu____3630 uu____3631 -> (match (((uu____3630), (uu____3631))) with
| ((bv, uu____3645), (a, uu____3647)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (

let uu____3661 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____3661 (FStar_Syntax_Subst.subst subst)))
in (

let uu____3666 = (encode_term_pred None ty env app_tm)
in (match (uu____3666) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____3676 = (

let uu____3681 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____3686 = (

let uu____3688 = (

let uu____3689 = (

let uu____3690 = (

let uu____3691 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____3691))
in (Prims.strcat "partial_app_typing_" uu____3690))
in (varops.mk_unique uu____3689))
in Some (uu____3688))
in ((uu____3681), (Some ("Partial app typing")), (uu____3686))))
in FStar_SMTEncoding_Term.Assume (uu____3676))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____3709 = (lookup_free_var_sym env fv)
in (match (uu____3709) with
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

let uu____3747 = (

let uu____3748 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3748 Prims.snd))
in Some (uu____3747))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3757, FStar_Util.Inl (t), uu____3759) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3780, FStar_Util.Inr (c), uu____3782) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| uu____3803 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (

let uu____3823 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____3823))
in (

let uu____3824 = (curried_arrow_formals_comp head_type)
in (match (uu____3824) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____3849 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (Some (((formals), (c)))))
end
| uu____3861 -> begin
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

let uu____3894 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____3894) with
| (bs, body, opening) -> begin
(

let fallback = (fun uu____3909 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (

let uu____3914 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____3914), ((decl)::[]))))))
in (

let is_impure = (fun uu___117_3924 -> (match (uu___117_3924) with
| FStar_Util.Inl (lc) -> begin
(

let uu____3934 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (not (uu____3934)))
end
| FStar_Util.Inr (eff, uu____3936) -> begin
(

let uu____3942 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right uu____3942 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(

let uu____3963 = (

let uu____3964 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____3964))
in (FStar_All.pipe_right uu____3963 (fun _0_31 -> Some (_0_31))))
end
| FStar_Util.Inr (eff, flags) -> begin
(

let new_uvar = (fun uu____3976 -> (

let uu____3977 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____3977 Prims.fst)))
in (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(

let uu____3985 = (

let uu____3986 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total uu____3986))
in (FStar_All.pipe_right uu____3985 (fun _0_32 -> Some (_0_32))))
end
| uu____3988 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(

let uu____3990 = (

let uu____3991 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal uu____3991))
in (FStar_All.pipe_right uu____3990 (fun _0_33 -> Some (_0_33))))
end
| uu____3993 -> begin
None
end)
end))
end))
in (match (lopt) with
| None -> begin
((

let uu____4002 = (

let uu____4003 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____4003))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____4002));
(fallback ());
)
end
| Some (lc) -> begin
(

let uu____4015 = (is_impure lc)
in (match (uu____4015) with
| true -> begin
(fallback ())
end
| uu____4018 -> begin
(

let uu____4019 = (encode_binders None bs env)
in (match (uu____4019) with
| (vars, guards, envbody, decls, uu____4034) -> begin
(

let uu____4041 = (encode_term body envbody)
in (match (uu____4041) with
| (body, decls') -> begin
(

let key_body = (

let uu____4049 = (

let uu____4055 = (

let uu____4056 = (

let uu____4059 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____4059), (body)))
in (FStar_SMTEncoding_Util.mkImp uu____4056))
in (([]), (vars), (uu____4055)))
in (FStar_SMTEncoding_Util.mkForall uu____4049))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____4070 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____4070) with
| Some (t, uu____4085, uu____4086) -> begin
(

let uu____4096 = (

let uu____4097 = (

let uu____4101 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((t), (uu____4101)))
in (FStar_SMTEncoding_Util.mkApp uu____4097))
in ((uu____4096), ([])))
end
| None -> begin
(

let uu____4112 = (is_eta env vars body)
in (match (uu____4112) with
| Some (t) -> begin
((t), ([]))
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let fsym = (

let uu____4123 = (

let uu____4124 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____4124))
in (varops.mk_unique uu____4123))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (

let uu____4129 = (

let uu____4133 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((fsym), (uu____4133)))
in (FStar_SMTEncoding_Util.mkApp uu____4129))
in (

let app = (mk_Apply f vars)
in (

let typing_f = (

let uu____4141 = (codomain_eff lc)
in (match (uu____4141) with
| None -> begin
[]
end
| Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs c)
in (

let uu____4148 = (encode_term_pred None tfun env f)
in (match (uu____4148) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (

let uu____4156 = (

let uu____4158 = (

let uu____4159 = (

let uu____4164 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((uu____4164), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____4159))
in (uu____4158)::[])
in (FStar_List.append decls'' uu____4156)))
end)))
end))
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (

let uu____4174 = (

let uu____4179 = (

let uu____4180 = (

let uu____4186 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (uu____4186)))
in (FStar_SMTEncoding_Util.mkForall uu____4180))
in ((uu____4179), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____4174)))
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
| FStar_Syntax_Syntax.Tm_let ((uu____4205, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____4206); FStar_Syntax_Syntax.lbunivs = uu____4207; FStar_Syntax_Syntax.lbtyp = uu____4208; FStar_Syntax_Syntax.lbeff = uu____4209; FStar_Syntax_Syntax.lbdef = uu____4210})::uu____4211), uu____4212) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____4230; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____4232; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____4248) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let uu____4261 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____4261), ((decl_e)::[])))));
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____4303 = (encode_term e1 env)
in (match (uu____4303) with
| (ee1, decls1) -> begin
(

let uu____4310 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (uu____4310) with
| (xs, e2) -> begin
(

let uu____4324 = (FStar_List.hd xs)
in (match (uu____4324) with
| (x, uu____4332) -> begin
(

let env' = (push_term_var env x ee1)
in (

let uu____4334 = (encode_body e2 env')
in (match (uu____4334) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____4356 = (encode_term e env)
in (match (uu____4356) with
| (scr, decls) -> begin
(

let uu____4363 = (FStar_List.fold_right (fun b uu____4371 -> (match (uu____4371) with
| (else_case, decls) -> begin
(

let uu____4382 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____4382) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun uu____4412 uu____4413 -> (match (((uu____4412), (uu____4413))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr)
in (

let projections = (pattern.projections scr)
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env uu____4450 -> (match (uu____4450) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let uu____4455 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let uu____4470 = (encode_term w env)
in (match (uu____4470) with
| (w, decls2) -> begin
(

let uu____4478 = (

let uu____4479 = (

let uu____4482 = (

let uu____4483 = (

let uu____4486 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w), (uu____4486)))
in (FStar_SMTEncoding_Util.mkEq uu____4483))
in ((guard), (uu____4482)))
in (FStar_SMTEncoding_Util.mkAnd uu____4479))
in ((uu____4478), (decls2)))
end))
end)
in (match (uu____4455) with
| (guard, decls2) -> begin
(

let uu____4494 = (encode_br br env)
in (match (uu____4494) with
| (br, decls3) -> begin
(

let uu____4502 = (FStar_SMTEncoding_Util.mkITE ((guard), (br), (else_case)))
in ((uu____4502), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end)) pats ((default_case), (decls)))
in (match (uu____4363) with
| (match_tm, decls) -> begin
((match_tm), (decls))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| uu____4526 -> begin
(

let uu____4527 = (encode_one_pat env pat)
in (uu____4527)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____4539 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4539) with
| true -> begin
(

let uu____4540 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____4540))
end
| uu____4541 -> begin
()
end));
(

let uu____4542 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____4542) with
| (vars, pat_term) -> begin
(

let uu____4552 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____4575 v -> (match (uu____4575) with
| (env, vars) -> begin
(

let uu____4603 = (gen_term_var env v)
in (match (uu____4603) with
| (xx, uu____4615, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (uu____4552) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4662) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____4670 = (

let uu____4673 = (encode_const c)
in ((scrutinee), (uu____4673)))
in (FStar_SMTEncoding_Util.mkEq uu____4670))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4704 -> (match (uu____4704) with
| (arg, uu____4710) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____4720 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____4720)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4739) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____4754) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____4769 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4791 -> (match (uu____4791) with
| (arg, uu____4800) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____4810 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____4810)))
end))))
in (FStar_All.pipe_right uu____4769 FStar_List.flatten))
end))
in (

let pat_term = (fun uu____4826 -> (encode_term pat_term env))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____4833 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____4848 uu____4849 -> (match (((uu____4848), (uu____4849))) with
| ((tms, decls), (t, uu____4869)) -> begin
(

let uu____4880 = (encode_term t env)
in (match (uu____4880) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____4833) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let list_elements = (fun e -> (

let uu____4918 = (FStar_Syntax_Util.list_elements e)
in (match (uu____4918) with
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

let uu____4936 = (

let uu____4946 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____4946 FStar_Syntax_Util.head_and_args))
in (match (uu____4936) with
| (head, args) -> begin
(

let uu____4977 = (

let uu____4985 = (

let uu____4986 = (FStar_Syntax_Util.un_uinst head)
in uu____4986.FStar_Syntax_Syntax.n)
in ((uu____4985), (args)))
in (match (uu____4977) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____5000, uu____5001))::((e, uu____5003))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5034))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| uu____5055 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let uu____5088 = (

let uu____5098 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right uu____5098 FStar_Syntax_Util.head_and_args))
in (match (uu____5088) with
| (head, args) -> begin
(

let uu____5127 = (

let uu____5135 = (

let uu____5136 = (FStar_Syntax_Util.un_uinst head)
in uu____5136.FStar_Syntax_Syntax.n)
in ((uu____5135), (args)))
in (match (uu____5127) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5149))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| uu____5169 -> begin
None
end))
end)))
in (match (elts) with
| (t)::[] -> begin
(

let uu____5187 = (smt_pat_or t)
in (match (uu____5187) with
| Some (e) -> begin
(

let uu____5203 = (list_elements e)
in (FStar_All.pipe_right uu____5203 (FStar_List.map (fun branch -> (

let uu____5220 = (list_elements branch)
in (FStar_All.pipe_right uu____5220 (FStar_List.map one_pat)))))))
end
| uu____5234 -> begin
(

let uu____5238 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5238)::[])
end))
end
| uu____5269 -> begin
(

let uu____5271 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5271)::[])
end))))
in (

let uu____5302 = (

let uu____5318 = (

let uu____5319 = (FStar_Syntax_Subst.compress t)
in uu____5319.FStar_Syntax_Syntax.n)
in (match (uu____5318) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____5349 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____5349) with
| (binders, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____5384; FStar_Syntax_Syntax.effect_name = uu____5385; FStar_Syntax_Syntax.result_typ = uu____5386; FStar_Syntax_Syntax.effect_args = ((pre, uu____5388))::((post, uu____5390))::((pats, uu____5392))::[]; FStar_Syntax_Syntax.flags = uu____5393}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (

let uu____5427 = (lemma_pats pats')
in ((binders), (pre), (post), (uu____5427))))
end
| uu____5446 -> begin
(failwith "impos")
end)
end))
end
| uu____5462 -> begin
(failwith "Impos")
end))
in (match (uu____5302) with
| (binders, pre, post, patterns) -> begin
(

let uu____5506 = (encode_binders None binders env)
in (match (uu____5506) with
| (vars, guards, env, decls, uu____5521) -> begin
(

let uu____5528 = (

let uu____5535 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let uu____5566 = (

let uu____5571 = (FStar_All.pipe_right branch (FStar_List.map (fun uu____5587 -> (match (uu____5587) with
| (t, uu____5594) -> begin
(encode_term t (

let uu___143_5597 = env
in {bindings = uu___143_5597.bindings; depth = uu___143_5597.depth; tcenv = uu___143_5597.tcenv; warn = uu___143_5597.warn; cache = uu___143_5597.cache; nolabels = uu___143_5597.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___143_5597.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right uu____5571 FStar_List.unzip))
in (match (uu____5566) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right uu____5535 FStar_List.unzip))
in (match (uu____5528) with
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

let uu____5661 = (

let uu____5662 = (FStar_SMTEncoding_Util.mkFreeV l)
in (FStar_SMTEncoding_Util.mk_Precedes uu____5662 e))
in (uu____5661)::p))))
end
| uu____5663 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (

let uu____5692 = (FStar_SMTEncoding_Util.mk_Precedes tl e)
in (uu____5692)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(

let uu____5700 = (

let uu____5701 = (FStar_SMTEncoding_Util.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mk_LexCons uu____5701 tl))
in (aux uu____5700 vars))
end
| uu____5702 -> begin
pats
end))
in (

let uu____5706 = (FStar_SMTEncoding_Util.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux uu____5706 vars)))
end)
end)
in (

let env = (

let uu___144_5708 = env
in {bindings = uu___144_5708.bindings; depth = uu___144_5708.depth; tcenv = uu___144_5708.tcenv; warn = uu___144_5708.warn; cache = uu___144_5708.cache; nolabels = true; use_zfuel_name = uu___144_5708.use_zfuel_name; encode_non_total_function_typ = uu___144_5708.encode_non_total_function_typ})
in (

let uu____5709 = (

let uu____5712 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____5712 env))
in (match (uu____5709) with
| (pre, decls'') -> begin
(

let uu____5717 = (

let uu____5720 = (FStar_Syntax_Util.unmeta post)
in (encode_formula uu____5720 env))
in (match (uu____5717) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (

let uu____5727 = (

let uu____5728 = (

let uu____5734 = (

let uu____5735 = (

let uu____5738 = (FStar_SMTEncoding_Util.mk_and_l ((pre)::guards))
in ((uu____5738), (post)))
in (FStar_SMTEncoding_Util.mkImp uu____5735))
in ((pats), (vars), (uu____5734)))
in (FStar_SMTEncoding_Util.mkForall uu____5728))
in ((uu____5727), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> (

let uu____5751 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____5751) with
| true -> begin
(

let uu____5752 = (FStar_Syntax_Print.tag_of_term phi)
in (

let uu____5753 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____5752 uu____5753)))
end
| uu____5754 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____5780 = (FStar_Util.fold_map (fun decls x -> (

let uu____5793 = (encode_term (Prims.fst x) env)
in (match (uu____5793) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____5780) with
| (decls, args) -> begin
(

let uu____5810 = (

let uu___145_5811 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___145_5811.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___145_5811.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____5810), (decls)))
end)))
in (

let const_op = (fun f r uu____5830 -> (

let uu____5833 = (f r)
in ((uu____5833), ([]))))
in (

let un_op = (fun f l -> (

let uu____5849 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____5849)))
in (

let bin_op = (fun f uu___118_5862 -> (match (uu___118_5862) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____5870 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____5897 = (FStar_Util.fold_map (fun decls uu____5906 -> (match (uu____5906) with
| (t, uu____5914) -> begin
(

let uu____5915 = (encode_formula t env)
in (match (uu____5915) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (uu____5897) with
| (decls, phis) -> begin
(

let uu____5932 = (

let uu___146_5933 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___146_5933.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___146_5933.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____5932), (decls)))
end)))
in (

let eq_op = (fun r uu___119_5949 -> (match (uu___119_5949) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
((enc (bin_op FStar_SMTEncoding_Util.mkEq)) r ((e1)::(e2)::[]))
end
| l -> begin
((enc (bin_op FStar_SMTEncoding_Util.mkEq)) r l)
end))
in (

let mk_imp = (fun r uu___120_6034 -> (match (uu___120_6034) with
| ((lhs, uu____6038))::((rhs, uu____6040))::[] -> begin
(

let uu____6061 = (encode_formula rhs env)
in (match (uu____6061) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____6070) -> begin
((l1), (decls1))
end
| uu____6073 -> begin
(

let uu____6074 = (encode_formula lhs env)
in (match (uu____6074) with
| (l2, decls2) -> begin
(

let uu____6081 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____6081), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____6083 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___121_6098 -> (match (uu___121_6098) with
| ((guard, uu____6102))::((_then, uu____6104))::((_else, uu____6106))::[] -> begin
(

let uu____6135 = (encode_formula guard env)
in (match (uu____6135) with
| (g, decls1) -> begin
(

let uu____6142 = (encode_formula _then env)
in (match (uu____6142) with
| (t, decls2) -> begin
(

let uu____6149 = (encode_formula _else env)
in (match (uu____6149) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____6158 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____6177 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____6177)))
in (

let connectives = (

let uu____6189 = (

let uu____6198 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Syntax_Const.and_lid), (uu____6198)))
in (

let uu____6220 = (

let uu____6230 = (

let uu____6239 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Syntax_Const.or_lid), (uu____6239)))
in (

let uu____6261 = (

let uu____6271 = (

let uu____6281 = (

let uu____6290 = (FStar_All.pipe_left enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Syntax_Const.iff_lid), (uu____6290)))
in (

let uu____6312 = (

let uu____6322 = (

let uu____6332 = (

let uu____6341 = (FStar_All.pipe_left enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Syntax_Const.not_lid), (uu____6341)))
in (uu____6332)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::uu____6322)
in (uu____6281)::uu____6312))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::uu____6271)
in (uu____6230)::uu____6261))
in (uu____6189)::uu____6220))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____6512 = (encode_formula phi' env)
in (match (uu____6512) with
| (phi, decls) -> begin
(

let uu____6519 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))) r)
in ((uu____6519), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____6520) -> begin
(

let uu____6525 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula uu____6525 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____6554 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____6554) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____6562; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____6564; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____6580 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____6580) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____6612)::((x, uu____6614))::((t, uu____6616))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let uu____6650 = (encode_term x env)
in (match (uu____6650) with
| (x, decls) -> begin
(

let uu____6657 = (encode_term t env)
in (match (uu____6657) with
| (t, decls') -> begin
(

let uu____6664 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((uu____6664), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____6668))::((msg, uu____6670))::((phi, uu____6672))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(

let uu____6706 = (

let uu____6709 = (

let uu____6710 = (FStar_Syntax_Subst.compress r)
in uu____6710.FStar_Syntax_Syntax.n)
in (

let uu____6713 = (

let uu____6714 = (FStar_Syntax_Subst.compress msg)
in uu____6714.FStar_Syntax_Syntax.n)
in ((uu____6709), (uu____6713))))
in (match (uu____6706) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____6721))) -> begin
(

let phi = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false)))))))) None r)
in (fallback phi))
end
| uu____6737 -> begin
(fallback phi)
end))
end
| uu____6740 when (head_redex env head) -> begin
(

let uu____6748 = (whnf env phi)
in (encode_formula uu____6748 env))
end
| uu____6749 -> begin
(

let uu____6757 = (encode_term phi env)
in (match (uu____6757) with
| (tt, decls) -> begin
(

let uu____6764 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___147_6765 = tt
in {FStar_SMTEncoding_Term.tm = uu___147_6765.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___147_6765.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((uu____6764), (decls)))
end))
end))
end
| uu____6768 -> begin
(

let uu____6769 = (encode_term phi env)
in (match (uu____6769) with
| (tt, decls) -> begin
(

let uu____6776 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___148_6777 = tt
in {FStar_SMTEncoding_Term.tm = uu___148_6777.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___148_6777.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((uu____6776), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let uu____6804 = (encode_binders None bs env)
in (match (uu____6804) with
| (vars, guards, env, decls, uu____6826) -> begin
(

let uu____6833 = (

let uu____6840 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____6863 = (

let uu____6868 = (FStar_All.pipe_right p (FStar_List.map (fun uu____6882 -> (match (uu____6882) with
| (t, uu____6888) -> begin
(encode_term t (

let uu___149_6889 = env
in {bindings = uu___149_6889.bindings; depth = uu___149_6889.depth; tcenv = uu___149_6889.tcenv; warn = uu___149_6889.warn; cache = uu___149_6889.cache; nolabels = uu___149_6889.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___149_6889.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right uu____6868 FStar_List.unzip))
in (match (uu____6863) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right uu____6840 FStar_List.unzip))
in (match (uu____6833) with
| (pats, decls') -> begin
(

let uu____6941 = (encode_formula body env)
in (match (uu____6941) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____6960; FStar_SMTEncoding_Term.rng = uu____6961})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| uu____6969 -> begin
guards
end)
in (

let uu____6972 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((vars), (pats), (uu____6972), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug phi);
(

let phi = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun uu____7006 -> (match (uu____7006) with
| (x, uu____7010) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats) with
| [] -> begin
()
end
| (hd)::tl -> begin
(

let pat_vars = (

let uu____7016 = (FStar_Syntax_Free.names hd)
in (FStar_List.fold_left (fun out x -> (

let uu____7022 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____7022))) uu____7016 tl))
in (

let uu____7024 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____7036 -> (match (uu____7036) with
| (b, uu____7040) -> begin
(

let uu____7041 = (FStar_Util.set_mem b pat_vars)
in (not (uu____7041)))
end))))
in (match (uu____7024) with
| None -> begin
()
end
| Some (x, uu____7045) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd.FStar_Syntax_Syntax.pos tl)
in (

let uu____7055 = (

let uu____7056 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____7056))
in (FStar_Errors.warn pos uu____7055)))
end)))
end)))
in (

let uu____7057 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____7057) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____7063 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____7099 -> (match (uu____7099) with
| (l, uu____7109) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____7063) with
| None -> begin
(fallback phi)
end
| Some (uu____7132, f) -> begin
(f phi.FStar_Syntax_Syntax.pos arms)
end))
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7161 = (encode_q_body env vars pats body)
in (match (uu____7161) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (

let uu____7187 = (

let uu____7193 = (FStar_SMTEncoding_Util.mkImp ((guard), (body)))
in ((pats), (vars), (uu____7193)))
in (FStar_SMTEncoding_Term.mkForall uu____7187 phi.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7205 = (encode_q_body env vars pats body)
in (match (uu____7205) with
| (vars, pats, guard, body, decls) -> begin
(

let uu____7230 = (

let uu____7231 = (

let uu____7237 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body)))
in ((pats), (vars), (uu____7237)))
in (FStar_SMTEncoding_Term.mkExists uu____7231 phi.FStar_Syntax_Syntax.pos))
in ((uu____7230), (decls)))
end));
)
end))));
)))))))))))))))

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let prims : prims_t = (

let uu____7286 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7286) with
| (asym, a) -> begin
(

let uu____7291 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7291) with
| (xsym, x) -> begin
(

let uu____7296 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7296) with
| (ysym, y) -> begin
(

let quant = (fun vars body x -> (

let xname_decl = (

let uu____7326 = (

let uu____7332 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (uu____7332), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____7326))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (

let uu____7347 = (

let uu____7351 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x), (uu____7351)))
in (FStar_SMTEncoding_Util.mkApp uu____7347))
in (

let xtok = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (

let uu____7359 = (

let uu____7361 = (

let uu____7363 = (

let uu____7365 = (

let uu____7366 = (

let uu____7371 = (

let uu____7372 = (

let uu____7378 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____7378)))
in (FStar_SMTEncoding_Util.mkForall uu____7372))
in ((uu____7371), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (uu____7366))
in (

let uu____7388 = (

let uu____7390 = (

let uu____7391 = (

let uu____7396 = (

let uu____7397 = (

let uu____7403 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____7403)))
in (FStar_SMTEncoding_Util.mkForall uu____7397))
in ((uu____7396), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x)))))
in FStar_SMTEncoding_Term.Assume (uu____7391))
in (uu____7390)::[])
in (uu____7365)::uu____7388))
in (xtok_decl)::uu____7363)
in (xname_decl)::uu____7361)
in ((xtok), (uu____7359))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (

let uu____7453 = (

let uu____7461 = (

let uu____7467 = (

let uu____7468 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7468))
in (quant axy uu____7467))
in ((FStar_Syntax_Const.op_Eq), (uu____7461)))
in (

let uu____7474 = (

let uu____7483 = (

let uu____7491 = (

let uu____7497 = (

let uu____7498 = (

let uu____7499 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____7499))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7498))
in (quant axy uu____7497))
in ((FStar_Syntax_Const.op_notEq), (uu____7491)))
in (

let uu____7505 = (

let uu____7514 = (

let uu____7522 = (

let uu____7528 = (

let uu____7529 = (

let uu____7530 = (

let uu____7533 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7534 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7533), (uu____7534))))
in (FStar_SMTEncoding_Util.mkLT uu____7530))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7529))
in (quant xy uu____7528))
in ((FStar_Syntax_Const.op_LT), (uu____7522)))
in (

let uu____7540 = (

let uu____7549 = (

let uu____7557 = (

let uu____7563 = (

let uu____7564 = (

let uu____7565 = (

let uu____7568 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7569 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7568), (uu____7569))))
in (FStar_SMTEncoding_Util.mkLTE uu____7565))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7564))
in (quant xy uu____7563))
in ((FStar_Syntax_Const.op_LTE), (uu____7557)))
in (

let uu____7575 = (

let uu____7584 = (

let uu____7592 = (

let uu____7598 = (

let uu____7599 = (

let uu____7600 = (

let uu____7603 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7604 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7603), (uu____7604))))
in (FStar_SMTEncoding_Util.mkGT uu____7600))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7599))
in (quant xy uu____7598))
in ((FStar_Syntax_Const.op_GT), (uu____7592)))
in (

let uu____7610 = (

let uu____7619 = (

let uu____7627 = (

let uu____7633 = (

let uu____7634 = (

let uu____7635 = (

let uu____7638 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7639 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7638), (uu____7639))))
in (FStar_SMTEncoding_Util.mkGTE uu____7635))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7634))
in (quant xy uu____7633))
in ((FStar_Syntax_Const.op_GTE), (uu____7627)))
in (

let uu____7645 = (

let uu____7654 = (

let uu____7662 = (

let uu____7668 = (

let uu____7669 = (

let uu____7670 = (

let uu____7673 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7674 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7673), (uu____7674))))
in (FStar_SMTEncoding_Util.mkSub uu____7670))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7669))
in (quant xy uu____7668))
in ((FStar_Syntax_Const.op_Subtraction), (uu____7662)))
in (

let uu____7680 = (

let uu____7689 = (

let uu____7697 = (

let uu____7703 = (

let uu____7704 = (

let uu____7705 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____7705))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7704))
in (quant qx uu____7703))
in ((FStar_Syntax_Const.op_Minus), (uu____7697)))
in (

let uu____7711 = (

let uu____7720 = (

let uu____7728 = (

let uu____7734 = (

let uu____7735 = (

let uu____7736 = (

let uu____7739 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7740 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7739), (uu____7740))))
in (FStar_SMTEncoding_Util.mkAdd uu____7736))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7735))
in (quant xy uu____7734))
in ((FStar_Syntax_Const.op_Addition), (uu____7728)))
in (

let uu____7746 = (

let uu____7755 = (

let uu____7763 = (

let uu____7769 = (

let uu____7770 = (

let uu____7771 = (

let uu____7774 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7775 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7774), (uu____7775))))
in (FStar_SMTEncoding_Util.mkMul uu____7771))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7770))
in (quant xy uu____7769))
in ((FStar_Syntax_Const.op_Multiply), (uu____7763)))
in (

let uu____7781 = (

let uu____7790 = (

let uu____7798 = (

let uu____7804 = (

let uu____7805 = (

let uu____7806 = (

let uu____7809 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7810 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7809), (uu____7810))))
in (FStar_SMTEncoding_Util.mkDiv uu____7806))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7805))
in (quant xy uu____7804))
in ((FStar_Syntax_Const.op_Division), (uu____7798)))
in (

let uu____7816 = (

let uu____7825 = (

let uu____7833 = (

let uu____7839 = (

let uu____7840 = (

let uu____7841 = (

let uu____7844 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7845 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7844), (uu____7845))))
in (FStar_SMTEncoding_Util.mkMod uu____7841))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7840))
in (quant xy uu____7839))
in ((FStar_Syntax_Const.op_Modulus), (uu____7833)))
in (

let uu____7851 = (

let uu____7860 = (

let uu____7868 = (

let uu____7874 = (

let uu____7875 = (

let uu____7876 = (

let uu____7879 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____7880 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____7879), (uu____7880))))
in (FStar_SMTEncoding_Util.mkAnd uu____7876))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7875))
in (quant xy uu____7874))
in ((FStar_Syntax_Const.op_And), (uu____7868)))
in (

let uu____7886 = (

let uu____7895 = (

let uu____7903 = (

let uu____7909 = (

let uu____7910 = (

let uu____7911 = (

let uu____7914 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____7915 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____7914), (uu____7915))))
in (FStar_SMTEncoding_Util.mkOr uu____7911))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7910))
in (quant xy uu____7909))
in ((FStar_Syntax_Const.op_Or), (uu____7903)))
in (

let uu____7921 = (

let uu____7930 = (

let uu____7938 = (

let uu____7944 = (

let uu____7945 = (

let uu____7946 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____7946))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7945))
in (quant qx uu____7944))
in ((FStar_Syntax_Const.op_Negation), (uu____7938)))
in (uu____7930)::[])
in (uu____7895)::uu____7921))
in (uu____7860)::uu____7886))
in (uu____7825)::uu____7851))
in (uu____7790)::uu____7816))
in (uu____7755)::uu____7781))
in (uu____7720)::uu____7746))
in (uu____7689)::uu____7711))
in (uu____7654)::uu____7680))
in (uu____7619)::uu____7645))
in (uu____7584)::uu____7610))
in (uu____7549)::uu____7575))
in (uu____7514)::uu____7540))
in (uu____7483)::uu____7505))
in (uu____7453)::uu____7474))
in (

let mk = (fun l v -> (

let uu____8074 = (

let uu____8079 = (FStar_All.pipe_right prims (FStar_List.find (fun uu____8111 -> (match (uu____8111) with
| (l', uu____8120) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____8079 (FStar_Option.map (fun uu____8153 -> (match (uu____8153) with
| (uu____8164, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right uu____8074 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun uu____8205 -> (match (uu____8205) with
| (l', uu____8214) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let uu____8237 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____8237) with
| (xxsym, xx) -> begin
(

let uu____8242 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____8242) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let uu____8249 = (

let uu____8254 = (

let uu____8255 = (

let uu____8261 = (

let uu____8262 = (

let uu____8265 = (

let uu____8266 = (

let uu____8269 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____8269)))
in (FStar_SMTEncoding_Util.mkEq uu____8266))
in ((xx_has_type), (uu____8265)))
in (FStar_SMTEncoding_Util.mkImp uu____8262))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____8261)))
in (FStar_SMTEncoding_Util.mkForall uu____8255))
in (

let uu____8282 = (

let uu____8284 = (

let uu____8285 = (

let uu____8286 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "pretyping_" uu____8286))
in (varops.mk_unique uu____8285))
in Some (uu____8284))
in ((uu____8254), (Some ("pretyping")), (uu____8282))))
in FStar_SMTEncoding_Term.Assume (uu____8249))))
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

let uu____8317 = (

let uu____8318 = (

let uu____8323 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____8323), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8318))
in (

let uu____8326 = (

let uu____8328 = (

let uu____8329 = (

let uu____8334 = (

let uu____8335 = (

let uu____8341 = (

let uu____8342 = (

let uu____8345 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____8345)))
in (FStar_SMTEncoding_Util.mkImp uu____8342))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8341)))
in (mkForall_fuel uu____8335))
in ((uu____8334), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8329))
in (uu____8328)::[])
in (uu____8317)::uu____8326))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8374 = (

let uu____8375 = (

let uu____8380 = (

let uu____8381 = (

let uu____8387 = (

let uu____8390 = (

let uu____8392 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____8392)::[])
in (uu____8390)::[])
in (

let uu____8395 = (

let uu____8396 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8396 tt))
in ((uu____8387), ((bb)::[]), (uu____8395))))
in (FStar_SMTEncoding_Util.mkForall uu____8381))
in ((uu____8380), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8375))
in (

let uu____8408 = (

let uu____8410 = (

let uu____8411 = (

let uu____8416 = (

let uu____8417 = (

let uu____8423 = (

let uu____8424 = (

let uu____8427 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (uu____8427)))
in (FStar_SMTEncoding_Util.mkImp uu____8424))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8423)))
in (mkForall_fuel uu____8417))
in ((uu____8416), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8411))
in (uu____8410)::[])
in (uu____8374)::uu____8408))))))
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

let uu____8462 = (

let uu____8463 = (

let uu____8467 = (

let uu____8469 = (

let uu____8471 = (

let uu____8473 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____8474 = (

let uu____8476 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8476)::[])
in (uu____8473)::uu____8474))
in (tt)::uu____8471)
in (tt)::uu____8469)
in (("Prims.Precedes"), (uu____8467)))
in (FStar_SMTEncoding_Util.mkApp uu____8463))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8462))
in (

let precedes_y_x = (

let uu____8479 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8479))
in (

let uu____8481 = (

let uu____8482 = (

let uu____8487 = (

let uu____8488 = (

let uu____8494 = (

let uu____8497 = (

let uu____8499 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8499)::[])
in (uu____8497)::[])
in (

let uu____8502 = (

let uu____8503 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8503 tt))
in ((uu____8494), ((bb)::[]), (uu____8502))))
in (FStar_SMTEncoding_Util.mkForall uu____8488))
in ((uu____8487), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8482))
in (

let uu____8515 = (

let uu____8517 = (

let uu____8518 = (

let uu____8523 = (

let uu____8524 = (

let uu____8530 = (

let uu____8531 = (

let uu____8534 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (uu____8534)))
in (FStar_SMTEncoding_Util.mkImp uu____8531))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8530)))
in (mkForall_fuel uu____8524))
in ((uu____8523), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8518))
in (

let uu____8548 = (

let uu____8550 = (

let uu____8551 = (

let uu____8556 = (

let uu____8557 = (

let uu____8563 = (

let uu____8564 = (

let uu____8567 = (

let uu____8568 = (

let uu____8570 = (

let uu____8572 = (

let uu____8574 = (

let uu____8575 = (

let uu____8578 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____8579 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8578), (uu____8579))))
in (FStar_SMTEncoding_Util.mkGT uu____8575))
in (

let uu____8580 = (

let uu____8582 = (

let uu____8583 = (

let uu____8586 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8587 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8586), (uu____8587))))
in (FStar_SMTEncoding_Util.mkGTE uu____8583))
in (

let uu____8588 = (

let uu____8590 = (

let uu____8591 = (

let uu____8594 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8595 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____8594), (uu____8595))))
in (FStar_SMTEncoding_Util.mkLT uu____8591))
in (uu____8590)::[])
in (uu____8582)::uu____8588))
in (uu____8574)::uu____8580))
in (typing_pred_y)::uu____8572)
in (typing_pred)::uu____8570)
in (FStar_SMTEncoding_Util.mk_and_l uu____8568))
in ((uu____8567), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____8564))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____8563)))
in (mkForall_fuel uu____8557))
in ((uu____8556), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (uu____8551))
in (uu____8550)::[])
in (uu____8517)::uu____8548))
in (uu____8481)::uu____8515)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8626 = (

let uu____8627 = (

let uu____8632 = (

let uu____8633 = (

let uu____8639 = (

let uu____8642 = (

let uu____8644 = (FStar_SMTEncoding_Term.boxString b)
in (uu____8644)::[])
in (uu____8642)::[])
in (

let uu____8647 = (

let uu____8648 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8648 tt))
in ((uu____8639), ((bb)::[]), (uu____8647))))
in (FStar_SMTEncoding_Util.mkForall uu____8633))
in ((uu____8632), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8627))
in (

let uu____8660 = (

let uu____8662 = (

let uu____8663 = (

let uu____8668 = (

let uu____8669 = (

let uu____8675 = (

let uu____8676 = (

let uu____8679 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (uu____8679)))
in (FStar_SMTEncoding_Util.mkImp uu____8676))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8675)))
in (mkForall_fuel uu____8669))
in ((uu____8668), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8663))
in (uu____8662)::[])
in (uu____8626)::uu____8660))))))
in (

let mk_ref = (fun env reft_name uu____8702 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (

let uu____8713 = (

let uu____8717 = (

let uu____8719 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (uu____8719)::[])
in ((reft_name), (uu____8717)))
in (FStar_SMTEncoding_Util.mkApp uu____8713))
in (

let refb = (

let uu____8722 = (

let uu____8726 = (

let uu____8728 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (uu____8728)::[])
in ((reft_name), (uu____8726)))
in (FStar_SMTEncoding_Util.mkApp uu____8722))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (

let uu____8732 = (

let uu____8733 = (

let uu____8738 = (

let uu____8739 = (

let uu____8745 = (

let uu____8746 = (

let uu____8749 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (uu____8749)))
in (FStar_SMTEncoding_Util.mkImp uu____8746))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (uu____8745)))
in (mkForall_fuel uu____8739))
in ((uu____8738), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8733))
in (

let uu____8765 = (

let uu____8767 = (

let uu____8768 = (

let uu____8773 = (

let uu____8774 = (

let uu____8780 = (

let uu____8781 = (

let uu____8784 = (FStar_SMTEncoding_Util.mkAnd ((typing_pred), (typing_pred_b)))
in (

let uu____8785 = (

let uu____8786 = (

let uu____8789 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let uu____8790 = (FStar_SMTEncoding_Util.mkFreeV bb)
in ((uu____8789), (uu____8790))))
in (FStar_SMTEncoding_Util.mkEq uu____8786))
in ((uu____8784), (uu____8785))))
in (FStar_SMTEncoding_Util.mkImp uu____8781))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (uu____8780)))
in (mkForall_fuel' (Prims.parse_int "2") uu____8774))
in ((uu____8773), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (uu____8768))
in (uu____8767)::[])
in (uu____8732)::uu____8765))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), (Some ("true_interp")))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____8834 = (

let uu____8835 = (

let uu____8840 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____8840), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8835))
in (uu____8834)::[])))
in (

let mk_and_interp = (fun env conj uu____8852 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____8862 = (

let uu____8866 = (

let uu____8868 = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (uu____8868)::[])
in (("Valid"), (uu____8866)))
in (FStar_SMTEncoding_Util.mkApp uu____8862))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____8875 = (

let uu____8876 = (

let uu____8881 = (

let uu____8882 = (

let uu____8888 = (

let uu____8889 = (

let uu____8892 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____8892), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____8889))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____8888)))
in (FStar_SMTEncoding_Util.mkForall uu____8882))
in ((uu____8881), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8876))
in (uu____8875)::[])))))))))
in (

let mk_or_interp = (fun env disj uu____8917 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____8927 = (

let uu____8931 = (

let uu____8933 = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (uu____8933)::[])
in (("Valid"), (uu____8931)))
in (FStar_SMTEncoding_Util.mkApp uu____8927))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____8940 = (

let uu____8941 = (

let uu____8946 = (

let uu____8947 = (

let uu____8953 = (

let uu____8954 = (

let uu____8957 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____8957), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____8954))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____8953)))
in (FStar_SMTEncoding_Util.mkForall uu____8947))
in ((uu____8946), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8941))
in (uu____8940)::[])))))))))
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

let uu____8996 = (

let uu____9000 = (

let uu____9002 = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (uu____9002)::[])
in (("Valid"), (uu____9000)))
in (FStar_SMTEncoding_Util.mkApp uu____8996))
in (

let uu____9005 = (

let uu____9006 = (

let uu____9011 = (

let uu____9012 = (

let uu____9018 = (

let uu____9019 = (

let uu____9022 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((uu____9022), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9019))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (uu____9018)))
in (FStar_SMTEncoding_Util.mkForall uu____9012))
in ((uu____9011), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9006))
in (uu____9005)::[])))))))))
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

let uu____9067 = (

let uu____9071 = (

let uu____9073 = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (uu____9073)::[])
in (("Valid"), (uu____9071)))
in (FStar_SMTEncoding_Util.mkApp uu____9067))
in (

let uu____9076 = (

let uu____9077 = (

let uu____9082 = (

let uu____9083 = (

let uu____9089 = (

let uu____9090 = (

let uu____9093 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((uu____9093), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9090))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (uu____9089)))
in (FStar_SMTEncoding_Util.mkForall uu____9083))
in ((uu____9082), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9077))
in (uu____9076)::[])))))))))))
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

let uu____9132 = (

let uu____9136 = (

let uu____9138 = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (uu____9138)::[])
in (("Valid"), (uu____9136)))
in (FStar_SMTEncoding_Util.mkApp uu____9132))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9145 = (

let uu____9146 = (

let uu____9151 = (

let uu____9152 = (

let uu____9158 = (

let uu____9159 = (

let uu____9162 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____9162), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9159))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9158)))
in (FStar_SMTEncoding_Util.mkForall uu____9152))
in ((uu____9151), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9146))
in (uu____9145)::[])))))))))
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

let uu____9197 = (

let uu____9201 = (

let uu____9203 = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (uu____9203)::[])
in (("Valid"), (uu____9201)))
in (FStar_SMTEncoding_Util.mkApp uu____9197))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9210 = (

let uu____9211 = (

let uu____9216 = (

let uu____9217 = (

let uu____9223 = (

let uu____9224 = (

let uu____9227 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____9227), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9224))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9223)))
in (FStar_SMTEncoding_Util.mkForall uu____9217))
in ((uu____9216), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9211))
in (uu____9210)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let valid = (

let uu____9258 = (

let uu____9262 = (

let uu____9264 = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (uu____9264)::[])
in (("Valid"), (uu____9262)))
in (FStar_SMTEncoding_Util.mkApp uu____9258))
in (

let not_valid_a = (

let uu____9268 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9268))
in (

let uu____9270 = (

let uu____9271 = (

let uu____9276 = (

let uu____9277 = (

let uu____9283 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (uu____9283)))
in (FStar_SMTEncoding_Util.mkForall uu____9277))
in ((uu____9276), (Some ("not interpretation")), (Some ("l_not-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9271))
in (uu____9270)::[]))))))
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

let uu____9320 = (

let uu____9324 = (

let uu____9326 = (FStar_SMTEncoding_Util.mkApp ((for_all), ((a)::(b)::[])))
in (uu____9326)::[])
in (("Valid"), (uu____9324)))
in (FStar_SMTEncoding_Util.mkApp uu____9320))
in (

let valid_b_x = (

let uu____9330 = (

let uu____9334 = (

let uu____9336 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (uu____9336)::[])
in (("Valid"), (uu____9334)))
in (FStar_SMTEncoding_Util.mkApp uu____9330))
in (

let uu____9338 = (

let uu____9339 = (

let uu____9344 = (

let uu____9345 = (

let uu____9351 = (

let uu____9352 = (

let uu____9355 = (

let uu____9356 = (

let uu____9362 = (

let uu____9365 = (

let uu____9367 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (uu____9367)::[])
in (uu____9365)::[])
in (

let uu____9370 = (

let uu____9371 = (

let uu____9374 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((uu____9374), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9371))
in ((uu____9362), ((xx)::[]), (uu____9370))))
in (FStar_SMTEncoding_Util.mkForall uu____9356))
in ((uu____9355), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9352))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9351)))
in (FStar_SMTEncoding_Util.mkForall uu____9345))
in ((uu____9344), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9339))
in (uu____9338)::[]))))))))))
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

let uu____9422 = (

let uu____9426 = (

let uu____9428 = (FStar_SMTEncoding_Util.mkApp ((for_some), ((a)::(b)::[])))
in (uu____9428)::[])
in (("Valid"), (uu____9426)))
in (FStar_SMTEncoding_Util.mkApp uu____9422))
in (

let valid_b_x = (

let uu____9432 = (

let uu____9436 = (

let uu____9438 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (uu____9438)::[])
in (("Valid"), (uu____9436)))
in (FStar_SMTEncoding_Util.mkApp uu____9432))
in (

let uu____9440 = (

let uu____9441 = (

let uu____9446 = (

let uu____9447 = (

let uu____9453 = (

let uu____9454 = (

let uu____9457 = (

let uu____9458 = (

let uu____9464 = (

let uu____9467 = (

let uu____9469 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (uu____9469)::[])
in (uu____9467)::[])
in (

let uu____9472 = (

let uu____9473 = (

let uu____9476 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((uu____9476), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9473))
in ((uu____9464), ((xx)::[]), (uu____9472))))
in (FStar_SMTEncoding_Util.mkExists uu____9458))
in ((uu____9457), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9454))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9453)))
in (FStar_SMTEncoding_Util.mkForall uu____9447))
in ((uu____9446), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9441))
in (uu____9440)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____9513 = (

let uu____9514 = (

let uu____9519 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (

let uu____9520 = (

let uu____9522 = (varops.mk_unique "typing_range_const")
in Some (uu____9522))
in ((uu____9519), (Some ("Range_const typing")), (uu____9520))))
in FStar_SMTEncoding_Term.Assume (uu____9514))
in (uu____9513)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (

let uu____9785 = (FStar_Util.find_opt (fun uu____9803 -> (match (uu____9803) with
| (l, uu____9813) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)
in (match (uu____9785) with
| None -> begin
[]
end
| Some (uu____9835, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9872 = (encode_function_type_as_formula None None t env)
in (match (uu____9872) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9905 = ((

let uu____9906 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation uu____9906)) || (FStar_Syntax_Util.is_lemma t_norm))
in (match (uu____9905) with
| true -> begin
(

let uu____9910 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____9910) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (

let uu____9922 = (

let uu____9923 = (FStar_Syntax_Subst.compress t_norm)
in uu____9923.FStar_Syntax_Syntax.n)
in (match (uu____9922) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____9928) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____9945 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____9948 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env)))))
end))
end
| uu____9956 -> begin
(

let uu____9957 = (prims.is lid)
in (match (uu____9957) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____9962 = (prims.mk lid vname)
in (match (uu____9962) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end
| uu____9975 -> begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let uu____9977 = (

let uu____9983 = (curried_arrow_formals_comp t_norm)
in (match (uu____9983) with
| (args, comp) -> begin
(match (encode_non_total_function_typ) with
| true -> begin
(

let uu____9998 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (uu____9998)))
end
| uu____10005 -> begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end)
end))
in (match (uu____9977) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____10025 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____10025) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____10038 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___122_10062 -> (match (uu___122_10062) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____10065 = (FStar_Util.prefix vars)
in (match (uu____10065) with
| (uu____10076, (xxsym, uu____10078)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____10088 = (

let uu____10089 = (

let uu____10094 = (

let uu____10095 = (

let uu____10101 = (

let uu____10102 = (

let uu____10105 = (

let uu____10106 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____10106))
in ((vapp), (uu____10105)))
in (FStar_SMTEncoding_Util.mkEq uu____10102))
in ((((vapp)::[])::[]), (vars), (uu____10101)))
in (FStar_SMTEncoding_Util.mkForall uu____10095))
in ((uu____10094), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (uu____10089))
in (uu____10088)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____10118 = (FStar_Util.prefix vars)
in (match (uu____10118) with
| (uu____10129, (xxsym, uu____10131)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____10145 = (

let uu____10146 = (

let uu____10151 = (

let uu____10152 = (

let uu____10158 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____10158)))
in (FStar_SMTEncoding_Util.mkForall uu____10152))
in ((uu____10151), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (uu____10146))
in (uu____10145)::[])))))
end))
end
| uu____10168 -> begin
[]
end)))))
in (

let uu____10169 = (encode_binders None formals env)
in (match (uu____10169) with
| (vars, guards, env', decls1, uu____10185) -> begin
(

let uu____10192 = (match (pre_opt) with
| None -> begin
(

let uu____10197 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____10197), (decls1)))
end
| Some (p) -> begin
(

let uu____10199 = (encode_formula p env')
in (match (uu____10199) with
| (g, ds) -> begin
(

let uu____10206 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____10206), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____10192) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____10215 = (

let uu____10219 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____10219)))
in (FStar_SMTEncoding_Util.mkApp uu____10215))
in (

let uu____10224 = (

let vname_decl = (

let uu____10229 = (

let uu____10235 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____10240 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____10235), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____10229))
in (

let uu____10245 = (

let env = (

let uu___150_10249 = env
in {bindings = uu___150_10249.bindings; depth = uu___150_10249.depth; tcenv = uu___150_10249.tcenv; warn = uu___150_10249.warn; cache = uu___150_10249.cache; nolabels = uu___150_10249.nolabels; use_zfuel_name = uu___150_10249.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (

let uu____10250 = (

let uu____10251 = (head_normal env tt)
in (not (uu____10251)))
in (match (uu____10250) with
| true -> begin
(encode_term_pred None tt env vtok_tm)
end
| uu____10254 -> begin
(encode_term_pred None t_norm env vtok_tm)
end)))
in (match (uu____10245) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let uu____10263 = (match (formals) with
| [] -> begin
(

let uu____10272 = (

let uu____10273 = (

let uu____10275 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_34 -> Some (_0_34)) uu____10275))
in (push_free_var env lid vname uu____10273))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (uu____10272)))
end
| uu____10278 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (

let uu____10283 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) uu____10283))
in (

let name_tok_corr = (

let uu____10285 = (

let uu____10290 = (

let uu____10291 = (

let uu____10297 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____10297)))
in (FStar_SMTEncoding_Util.mkForall uu____10291))
in ((uu____10290), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (uu____10285))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (uu____10263) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (uu____10224) with
| (decls2, env) -> begin
(

let uu____10322 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let uu____10327 = (encode_term res_t env')
in (match (uu____10327) with
| (encoded_res_t, decls) -> begin
(

let uu____10335 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____10335), (decls)))
end)))
in (match (uu____10322) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____10343 = (

let uu____10348 = (

let uu____10349 = (

let uu____10355 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____10355)))
in (FStar_SMTEncoding_Util.mkForall uu____10349))
in ((uu____10348), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (uu____10343))
in (

let freshness = (

let uu____10365 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____10365) with
| true -> begin
(

let uu____10368 = (

let uu____10369 = (

let uu____10375 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (

let uu____10381 = (varops.next_id ())
in ((vname), (uu____10375), (FStar_SMTEncoding_Term.Term_sort), (uu____10381))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____10369))
in (

let uu____10383 = (

let uu____10385 = (pretype_axiom vapp vars)
in (uu____10385)::[])
in (uu____10368)::uu____10383))
end
| uu____10386 -> begin
[]
end))
in (

let g = (

let uu____10389 = (

let uu____10391 = (

let uu____10393 = (

let uu____10395 = (

let uu____10397 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____10397)
in (FStar_List.append freshness uu____10395))
in (FStar_List.append decls3 uu____10393))
in (FStar_List.append decls2 uu____10391))
in (FStar_List.append decls1 uu____10389))
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

let uu____10419 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10419) with
| None -> begin
(

let uu____10442 = (encode_free_var env x t t_norm [])
in (match (uu____10442) with
| (decls, env) -> begin
(

let uu____10457 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10457) with
| (n, x', uu____10476) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, uu____10488) -> begin
((((n), (x))), ([]), (env))
end)))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let uu____10521 = (encode_free_var env lid t tt quals)
in (match (uu____10521) with
| (decls, env) -> begin
(

let uu____10532 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____10532) with
| true -> begin
(

let uu____10536 = (

let uu____10538 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls uu____10538))
in ((uu____10536), (env)))
end
| uu____10541 -> begin
((decls), (env))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____10566 lb -> (match (uu____10566) with
| (decls, env) -> begin
(

let uu____10578 = (

let uu____10582 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env uu____10582 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____10578) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____10606 quals -> (match (uu____10606) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____10655 = (FStar_Util.first_N nbinders formals)
in (match (uu____10655) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun uu____10695 uu____10696 -> (match (((uu____10695), (uu____10696))) with
| ((formal, uu____10706), (binder, uu____10708)) -> begin
(

let uu____10713 = (

let uu____10718 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____10718)))
in FStar_Syntax_Syntax.NT (uu____10713))
end)) formals binders)
in (

let extra_formals = (

let uu____10723 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____10737 -> (match (uu____10737) with
| (x, i) -> begin
(

let uu____10744 = (

let uu___151_10745 = x
in (

let uu____10746 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___151_10745.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___151_10745.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____10746}))
in ((uu____10744), (i)))
end))))
in (FStar_All.pipe_right uu____10723 FStar_Syntax_Util.name_binders))
in (

let body = (

let uu____10758 = (

let uu____10760 = (

let uu____10761 = (FStar_Syntax_Subst.subst subst t)
in uu____10761.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _0_35 -> Some (_0_35)) uu____10760))
in (

let uu____10765 = (

let uu____10766 = (FStar_Syntax_Subst.compress body)
in (

let uu____10767 = (

let uu____10768 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd uu____10768))
in (FStar_Syntax_Syntax.extend_app_n uu____10766 uu____10767)))
in (uu____10765 uu____10758 body.FStar_Syntax_Syntax.pos)))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (

let uu____10856 = (

let uu____10857 = (FStar_Syntax_Util.unascribe e)
in uu____10857.FStar_Syntax_Syntax.n)
in (match (uu____10856) with
| FStar_Syntax_Syntax.Tm_abs (binders, body, lopt) -> begin
(

let uu____10899 = (FStar_Syntax_Subst.open_term' binders body)
in (match (uu____10899) with
| (binders, body, opening) -> begin
(

let uu____10920 = (

let uu____10921 = (FStar_Syntax_Subst.compress t_norm)
in uu____10921.FStar_Syntax_Syntax.n)
in (match (uu____10920) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____10950 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____10950) with
| (formals, c) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (FStar_Syntax_Util.comp_result c)
in (

let uu____10980 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c))
in (match (uu____10980) with
| true -> begin
(

let lopt = (subst_lcomp_opt opening lopt)
in (

let uu____11010 = (FStar_Util.first_N nformals binders)
in (match (uu____11010) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun uu____11058 uu____11059 -> (match (((uu____11058), (uu____11059))) with
| ((b, uu____11069), (x, uu____11071)) -> begin
(

let uu____11076 = (

let uu____11081 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (uu____11081)))
in FStar_Syntax_Syntax.NT (uu____11076))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))), (false))))
end)))
end
| uu____11103 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____11123 = (eta_expand binders formals body tres)
in (match (uu____11123) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end))
end
| uu____11175 -> begin
((((binders), (body), (formals), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____11185) -> begin
(

let uu____11190 = (

let uu____11203 = (aux norm x.FStar_Syntax_Syntax.sort)
in (Prims.fst uu____11203))
in ((uu____11190), (true)))
end
| uu____11242 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| uu____11244 -> begin
(

let uu____11245 = (

let uu____11246 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11247 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____11246 uu____11247)))
in (failwith uu____11245))
end))
end))
end
| uu____11262 -> begin
(

let uu____11263 = (

let uu____11264 = (FStar_Syntax_Subst.compress t_norm)
in uu____11264.FStar_Syntax_Syntax.n)
in (match (uu____11263) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____11293 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____11293) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let uu____11315 = (eta_expand [] formals e tres)
in (match (uu____11315) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end)))
end))
end
| uu____11369 -> begin
(((([]), (e), ([]), (t_norm))), (false))
end))
end)))
in (aux false t_norm)))
in try
(match (()) with
| () -> begin
(

let uu____11397 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp))))
in (match (uu____11397) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____11403 -> begin
(

let uu____11404 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____11445 lb -> (match (uu____11445) with
| (toks, typs, decls, env) -> begin
((

let uu____11496 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____11496) with
| true -> begin
(Prims.raise Let_rec_unencodeable)
end
| uu____11497 -> begin
()
end));
(

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____11499 = (

let uu____11507 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env uu____11507 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____11499) with
| (tok, decl, env) -> begin
(

let uu____11532 = (

let uu____11539 = (

let uu____11545 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((uu____11545), (tok)))
in (uu____11539)::toks)
in ((uu____11532), ((t_norm)::typs), ((decl)::decls), (env)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____11404) with
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
| uu____11647 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| Some (ftok) -> begin
(mk_Apply ftok vars)
end
| None -> begin
(

let uu____11652 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____11652 vars))
end)
end
| uu____11653 -> begin
(

let uu____11654 = (

let uu____11658 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____11658)))
in (FStar_SMTEncoding_Util.mkApp uu____11654))
end)
end))
in (

let uu____11663 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___123_11665 -> (match (uu___123_11665) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____11666 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (

let uu____11669 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation uu____11669))))))
in (match (uu____11663) with
| true -> begin
((decls), (env))
end
| uu____11674 -> begin
(match ((not (is_rec))) with
| true -> begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = uu____11689; FStar_Syntax_Syntax.lbunivs = uu____11690; FStar_Syntax_Syntax.lbtyp = uu____11691; FStar_Syntax_Syntax.lbeff = uu____11692; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____11734 = (destruct_bound_function flid t_norm e)
in (match (uu____11734) with
| ((binders, body, uu____11754, uu____11755), curry) -> begin
(

let uu____11785 = (encode_binders None binders env)
in (match (uu____11785) with
| (vars, guards, env', binder_decls, uu____11801) -> begin
(

let app = (mk_app curry f ftok vars)
in (

let uu____11809 = (

let uu____11814 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____11814) with
| true -> begin
(

let uu____11820 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____11821 = (encode_formula body env')
in ((uu____11820), (uu____11821))))
end
| uu____11826 -> begin
(

let uu____11827 = (encode_term body env')
in ((app), (uu____11827)))
end))
in (match (uu____11809) with
| (app, (body, decls2)) -> begin
(

let eqn = (

let uu____11841 = (

let uu____11846 = (

let uu____11847 = (

let uu____11853 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (uu____11853)))
in (FStar_SMTEncoding_Util.mkForall uu____11847))
in (

let uu____11859 = (

let uu____11861 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (uu____11861))
in ((uu____11846), (uu____11859), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (uu____11841))
in (

let uu____11864 = (

let uu____11866 = (

let uu____11868 = (

let uu____11870 = (

let uu____11872 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) uu____11872))
in (FStar_List.append decls2 uu____11870))
in (FStar_List.append binder_decls uu____11868))
in (FStar_List.append decls uu____11866))
in ((uu____11864), (env))))
end)))
end))
end))))
end
| uu____11875 -> begin
(failwith "Impossible")
end)
end
| uu____11890 -> begin
(

let fuel = (

let uu____11894 = (varops.fresh "fuel")
in ((uu____11894), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env
in (

let uu____11897 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun uu____11936 uu____11937 -> (match (((uu____11936), (uu____11937))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (

let uu____12019 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____12019))
in (

let gtok = (

let uu____12021 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____12021))
in (

let env = (

let uu____12023 = (

let uu____12025 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_36 -> Some (_0_36)) uu____12025))
in (push_free_var env flid gtok uu____12023))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (uu____11897) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 uu____12109 t_norm uu____12111 -> (match (((uu____12109), (uu____12111))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = uu____12134; FStar_Syntax_Syntax.lbunivs = uu____12135; FStar_Syntax_Syntax.lbtyp = uu____12136; FStar_Syntax_Syntax.lbeff = uu____12137; FStar_Syntax_Syntax.lbdef = e}) -> begin
(

let uu____12154 = (destruct_bound_function flid t_norm e)
in (match (uu____12154) with
| ((binders, body, formals, tres), curry) -> begin
((match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____12208 -> begin
()
end);
(

let uu____12209 = (encode_binders None binders env)
in (match (uu____12209) with
| (vars, guards, env', binder_decls, uu____12227) -> begin
(

let decl_g = (

let uu____12235 = (

let uu____12241 = (

let uu____12243 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____12243)
in ((g), (uu____12241), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____12235))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____12258 = (

let uu____12262 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____12262)))
in (FStar_SMTEncoding_Util.mkApp uu____12258))
in (

let gsapp = (

let uu____12268 = (

let uu____12272 = (

let uu____12274 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____12274)::vars_tm)
in ((g), (uu____12272)))
in (FStar_SMTEncoding_Util.mkApp uu____12268))
in (

let gmax = (

let uu____12278 = (

let uu____12282 = (

let uu____12284 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____12284)::vars_tm)
in ((g), (uu____12282)))
in (FStar_SMTEncoding_Util.mkApp uu____12278))
in (

let uu____12287 = (encode_term body env')
in (match (uu____12287) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____12298 = (

let uu____12303 = (

let uu____12304 = (

let uu____12312 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____12312)))
in (FStar_SMTEncoding_Util.mkForall' uu____12304))
in (

let uu____12323 = (

let uu____12325 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (uu____12325))
in ((uu____12303), (uu____12323), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (uu____12298))
in (

let eqn_f = (

let uu____12329 = (

let uu____12334 = (

let uu____12335 = (

let uu____12341 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____12341)))
in (FStar_SMTEncoding_Util.mkForall uu____12335))
in ((uu____12334), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12329))
in (

let eqn_g' = (

let uu____12350 = (

let uu____12355 = (

let uu____12356 = (

let uu____12362 = (

let uu____12363 = (

let uu____12366 = (

let uu____12367 = (

let uu____12371 = (

let uu____12373 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____12373)::vars_tm)
in ((g), (uu____12371)))
in (FStar_SMTEncoding_Util.mkApp uu____12367))
in ((gsapp), (uu____12366)))
in (FStar_SMTEncoding_Util.mkEq uu____12363))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____12362)))
in (FStar_SMTEncoding_Util.mkForall uu____12356))
in ((uu____12355), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12350))
in (

let uu____12386 = (

let uu____12391 = (encode_binders None formals env0)
in (match (uu____12391) with
| (vars, v_guards, env, binder_decls, uu____12408) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (

let uu____12423 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____12423 ((fuel)::vars)))
in (

let uu____12426 = (

let uu____12431 = (

let uu____12432 = (

let uu____12438 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (uu____12438)))
in (FStar_SMTEncoding_Util.mkForall uu____12432))
in ((uu____12431), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (uu____12426)))
in (

let uu____12450 = (

let uu____12454 = (encode_term_pred None tres env gapp)
in (match (uu____12454) with
| (g_typing, d3) -> begin
(

let uu____12462 = (

let uu____12464 = (

let uu____12465 = (

let uu____12470 = (

let uu____12471 = (

let uu____12477 = (

let uu____12478 = (

let uu____12481 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____12481), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____12478))
in ((((gapp)::[])::[]), ((fuel)::vars), (uu____12477)))
in (FStar_SMTEncoding_Util.mkForall uu____12471))
in ((uu____12470), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12465))
in (uu____12464)::[])
in ((d3), (uu____12462)))
end))
in (match (uu____12450) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____12386) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end));
)
end))
end))
in (

let uu____12517 = (

let uu____12524 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun uu____12556 uu____12557 -> (match (((uu____12556), (uu____12557))) with
| ((decls, eqns, env0), (gtok, ty, bs)) -> begin
(

let uu____12633 = (encode_one_binding env0 gtok ty bs)
in (match (uu____12633) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) uu____12524))
in (match (uu____12517) with
| (decls, eqns, env0) -> begin
(

let uu____12673 = (

let uu____12678 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right uu____12678 (FStar_List.partition (fun uu___124_12688 -> (match (uu___124_12688) with
| FStar_SMTEncoding_Term.DeclFun (uu____12689) -> begin
true
end
| uu____12695 -> begin
false
end)))))
in (match (uu____12673) with
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

let uu____12713 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____12713 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> ((

let uu____12746 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12746) with
| true -> begin
(

let uu____12747 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") uu____12747))
end
| uu____12748 -> begin
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

let uu____12751 = (encode_sigelt' env se)
in (match (uu____12751) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(

let uu____12760 = (

let uu____12762 = (

let uu____12763 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12763))
in (uu____12762)::[])
in ((uu____12760), (e)))
end
| uu____12765 -> begin
(

let uu____12766 = (

let uu____12768 = (

let uu____12770 = (

let uu____12771 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12771))
in (uu____12770)::g)
in (

let uu____12772 = (

let uu____12774 = (

let uu____12775 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12775))
in (uu____12774)::[])
in (FStar_List.append uu____12768 uu____12772)))
in ((uu____12766), (e)))
end)
end)));
))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (

let should_skip = (fun l -> false)
in (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____12787) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, uu____12798) -> begin
(

let uu____12799 = (

let uu____12800 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____12800 Prims.op_Negation))
in (match (uu____12799) with
| true -> begin
(([]), (env))
end
| uu____12805 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____12820 -> begin
(

let uu____12821 = (

let uu____12824 = (

let uu____12825 = (

let uu____12840 = (FStar_All.pipe_left (fun _0_37 -> Some (_0_37)) (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (uu____12840)))
in FStar_Syntax_Syntax.Tm_abs (uu____12825))
in (FStar_Syntax_Syntax.mk uu____12824))
in (uu____12821 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env a -> (

let uu____12893 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (uu____12893) with
| (aname, atok, env) -> begin
(

let uu____12903 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____12903) with
| (formals, uu____12913) -> begin
(

let uu____12920 = (

let uu____12923 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____12923 env))
in (match (uu____12920) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____12931 = (

let uu____12932 = (

let uu____12938 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____12946 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____12938), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____12932))
in (uu____12931)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let uu____12953 = (

let uu____12960 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____12980 -> (match (uu____12980) with
| (bv, uu____12988) -> begin
(

let uu____12989 = (gen_term_var env bv)
in (match (uu____12989) with
| (xxsym, xx, uu____12999) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right uu____12960 FStar_List.split))
in (match (uu____12953) with
| (xs_sorts, xs) -> begin
(

let app = (

let uu____13029 = (

let uu____13033 = (

let uu____13035 = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (uu____13035)::[])
in (("Reify"), (uu____13033)))
in (FStar_SMTEncoding_Util.mkApp uu____13029))
in (

let a_eq = (

let uu____13039 = (

let uu____13044 = (

let uu____13045 = (

let uu____13051 = (

let uu____13052 = (

let uu____13055 = (mk_Apply tm xs_sorts)
in ((app), (uu____13055)))
in (FStar_SMTEncoding_Util.mkEq uu____13052))
in ((((app)::[])::[]), (xs_sorts), (uu____13051)))
in (FStar_SMTEncoding_Util.mkForall uu____13045))
in ((uu____13044), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (uu____13039))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____13068 = (

let uu____13073 = (

let uu____13074 = (

let uu____13080 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____13080)))
in (FStar_SMTEncoding_Util.mkForall uu____13074))
in ((uu____13073), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (uu____13068))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____13091 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____13091) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13107, uu____13108, uu____13109, uu____13110) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let uu____13113 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____13113) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13124, t, quals, uu____13127) -> begin
(

let will_encode_definition = (

let uu____13131 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___125_13133 -> (match (uu___125_13133) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| uu____13136 -> begin
false
end))))
in (not (uu____13131)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____13140 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____13142 = (encode_top_level_val env fv t quals)
in (match (uu____13142) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____13154 = (

let uu____13156 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls uu____13156))
in ((uu____13154), (env)))))
end)))
end))
end
| FStar_Syntax_Syntax.Sig_assume (l, f, uu____13161, uu____13162) -> begin
(

let uu____13165 = (encode_formula f env)
in (match (uu____13165) with
| (f, decls) -> begin
(

let g = (

let uu____13174 = (

let uu____13175 = (

let uu____13180 = (

let uu____13182 = (

let uu____13183 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____13183))
in Some (uu____13182))
in (

let uu____13184 = (

let uu____13186 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (uu____13186))
in ((f), (uu____13180), (uu____13184))))
in FStar_SMTEncoding_Term.Assume (uu____13175))
in (uu____13174)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, uu____13192, quals, uu____13194) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let uu____13202 = (FStar_Util.fold_map (fun env lb -> (

let lid = (

let uu____13209 = (

let uu____13214 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____13214.FStar_Syntax_Syntax.fv_name)
in uu____13209.FStar_Syntax_Syntax.v)
in (

let uu____13218 = (

let uu____13219 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____13219))
in (match (uu____13218) with
| true -> begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let uu____13238 = (encode_sigelt' env val_decl)
in (match (uu____13238) with
| (decls, env) -> begin
((env), (decls))
end)))
end
| uu____13245 -> begin
((env), ([]))
end)))) env (Prims.snd lbs))
in (match (uu____13202) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____13255, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = uu____13257; FStar_Syntax_Syntax.lbtyp = uu____13258; FStar_Syntax_Syntax.lbeff = uu____13259; FStar_Syntax_Syntax.lbdef = uu____13260})::[]), uu____13261, uu____13262, uu____13263, uu____13264) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let uu____13280 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____13280) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid_b2t_x = (

let uu____13298 = (

let uu____13302 = (

let uu____13304 = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (uu____13304)::[])
in (("Valid"), (uu____13302)))
in (FStar_SMTEncoding_Util.mkApp uu____13298))
in (

let decls = (

let uu____13309 = (

let uu____13311 = (

let uu____13312 = (

let uu____13317 = (

let uu____13318 = (

let uu____13324 = (

let uu____13325 = (

let uu____13328 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (uu____13328)))
in (FStar_SMTEncoding_Util.mkEq uu____13325))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (uu____13324)))
in (FStar_SMTEncoding_Util.mkForall uu____13318))
in ((uu____13317), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (uu____13312))
in (uu____13311)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::uu____13309)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____13346, uu____13347, uu____13348, quals, uu____13350) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___126_13358 -> (match (uu___126_13358) with
| FStar_Syntax_Syntax.Discriminator (uu____13359) -> begin
true
end
| uu____13360 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____13362, uu____13363, lids, quals, uu____13366) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____13375 = (

let uu____13376 = (FStar_List.hd l.FStar_Ident.ns)
in uu____13376.FStar_Ident.idText)
in (uu____13375 = "Prims"))))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___127_13378 -> (match (uu___127_13378) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____13379 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____13382, uu____13383, quals, uu____13385) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___128_13397 -> (match (uu___128_13397) with
| FStar_Syntax_Syntax.Projector (uu____13398) -> begin
true
end
| uu____13401 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____13408 = (try_lookup_free_var env l)
in (match (uu____13408) with
| Some (uu____13412) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((uu____13419, (lb)::[]), uu____13421, uu____13422, quals, uu____13424) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let uu____13436 = (

let uu____13437 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in uu____13437.FStar_Syntax_Syntax.n)
in (match (uu____13436) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____13444) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let uu____13501 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____13501) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let uu___154_13518 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___154_13518.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___154_13518.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___154_13518.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___154_13518.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___154_13518.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___154_13518.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___154_13518.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___154_13518.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___154_13518.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___154_13518.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___154_13518.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___154_13518.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___154_13518.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___154_13518.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___154_13518.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___154_13518.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___154_13518.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___154_13518.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___154_13518.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___154_13518.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___154_13518.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___154_13518.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___154_13518.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (

let uu____13519 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals uu____13519)))
end))
in (

let lb = (

let uu___155_13523 = lb
in {FStar_Syntax_Syntax.lbname = uu___155_13523.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___155_13523.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = uu___155_13523.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in ((

let uu____13525 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____13525) with
| true -> begin
(

let uu____13526 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____13527 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____13528 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print3 "%s: Reified %s\nto %s\n" uu____13526 uu____13527 uu____13528))))
end
| uu____13529 -> begin
()
end));
(encode_top_level_let env ((false), ((lb)::[])) quals);
))))))
end
| uu____13531 -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____13535, uu____13536, quals, uu____13538) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____13552, uu____13553, uu____13554) -> begin
(

let uu____13561 = (encode_signature env ses)
in (match (uu____13561) with
| (g, env) -> begin
(

let uu____13571 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___129_13581 -> (match (uu___129_13581) with
| FStar_SMTEncoding_Term.Assume (uu____13582, Some ("inversion axiom"), uu____13583) -> begin
false
end
| uu____13587 -> begin
true
end))))
in (match (uu____13571) with
| (g', inversions) -> begin
(

let uu____13596 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___130_13606 -> (match (uu___130_13606) with
| FStar_SMTEncoding_Term.DeclFun (uu____13607) -> begin
true
end
| uu____13613 -> begin
false
end))))
in (match (uu____13596) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____13624, tps, k, uu____13627, datas, quals, uu____13630) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___131_13639 -> (match (uu___131_13639) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| uu____13640 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____13663 = c
in (match (uu____13663) with
| (name, args, uu____13675, uu____13676, uu____13677) -> begin
(

let uu____13684 = (

let uu____13685 = (

let uu____13691 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (uu____13691), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____13685))
in (uu____13684)::[])
end))
end
| uu____13701 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____13716 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____13719 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____13719 FStar_Option.isNone)))))
in (match (uu____13716) with
| true -> begin
[]
end
| uu____13729 -> begin
(

let uu____13730 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13730) with
| (xxsym, xx) -> begin
(

let uu____13736 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____13747 l -> (match (uu____13747) with
| (out, decls) -> begin
(

let uu____13759 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____13759) with
| (uu____13765, data_t) -> begin
(

let uu____13767 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____13767) with
| (args, res) -> begin
(

let indices = (

let uu____13796 = (

let uu____13797 = (FStar_Syntax_Subst.compress res)
in uu____13797.FStar_Syntax_Syntax.n)
in (match (uu____13796) with
| FStar_Syntax_Syntax.Tm_app (uu____13805, indices) -> begin
indices
end
| uu____13821 -> begin
[]
end))
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env uu____13833 -> (match (uu____13833) with
| (x, uu____13837) -> begin
(

let uu____13838 = (

let uu____13839 = (

let uu____13843 = (mk_term_projector_name l x)
in ((uu____13843), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____13839))
in (push_term_var env x uu____13838))
end)) env))
in (

let uu____13845 = (encode_args indices env)
in (match (uu____13845) with
| (indices, decls') -> begin
((match (((FStar_List.length indices) <> (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____13863 -> begin
()
end);
(

let eqs = (

let uu____13865 = (FStar_List.map2 (fun v a -> (

let uu____13873 = (

let uu____13876 = (FStar_SMTEncoding_Util.mkFreeV v)
in ((uu____13876), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____13873))) vars indices)
in (FStar_All.pipe_right uu____13865 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____13878 = (

let uu____13879 = (

let uu____13882 = (

let uu____13883 = (

let uu____13886 = (mk_data_tester env l xx)
in ((uu____13886), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____13883))
in ((out), (uu____13882)))
in (FStar_SMTEncoding_Util.mkOr uu____13879))
in ((uu____13878), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____13736) with
| (data_ax, decls) -> begin
(

let uu____13894 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____13894) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____13905 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____13905 xx tapp))
end
| uu____13907 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____13908 = (

let uu____13913 = (

let uu____13914 = (

let uu____13920 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____13928 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____13920), (uu____13928))))
in (FStar_SMTEncoding_Util.mkForall uu____13914))
in (

let uu____13936 = (

let uu____13938 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (uu____13938))
in ((uu____13913), (Some ("inversion axiom")), (uu____13936))))
in FStar_SMTEncoding_Term.Assume (uu____13908)))
in (

let pattern_guarded_inversion = (

let uu____13943 = ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1")))
in (match (uu____13943) with
| true -> begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (

let uu____13951 = (

let uu____13952 = (

let uu____13957 = (

let uu____13958 = (

let uu____13964 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____13972 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (uu____13964), (uu____13972))))
in (FStar_SMTEncoding_Util.mkForall uu____13958))
in (

let uu____13980 = (

let uu____13982 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (uu____13982))
in ((uu____13957), (Some ("inversion axiom")), (uu____13980))))
in FStar_SMTEncoding_Term.Assume (uu____13952))
in (uu____13951)::[])))
end
| uu____13985 -> begin
[]
end))
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)))
in (

let uu____13986 = (

let uu____13994 = (

let uu____13995 = (FStar_Syntax_Subst.compress k)
in uu____13995.FStar_Syntax_Syntax.n)
in (match (uu____13994) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____14024 -> begin
((tps), (k))
end))
in (match (uu____13986) with
| (formals, res) -> begin
(

let uu____14039 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____14039) with
| (formals, res) -> begin
(

let uu____14046 = (encode_binders None formals env)
in (match (uu____14046) with
| (vars, guards, env', binder_decls, uu____14061) -> begin
(

let uu____14068 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____14068) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____14081 = (

let uu____14085 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____14085)))
in (FStar_SMTEncoding_Util.mkApp uu____14081))
in (

let uu____14090 = (

let tname_decl = (

let uu____14096 = (

let uu____14105 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____14117 -> (match (uu____14117) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (

let uu____14124 = (varops.next_id ())
in ((tname), (uu____14105), (FStar_SMTEncoding_Term.Term_sort), (uu____14124), (false))))
in (constructor_or_logic_type_decl uu____14096))
in (

let uu____14128 = (match (vars) with
| [] -> begin
(

let uu____14135 = (

let uu____14136 = (

let uu____14138 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_38 -> Some (_0_38)) uu____14138))
in (push_free_var env t tname uu____14136))
in (([]), (uu____14135)))
end
| uu____14142 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (

let uu____14148 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____14148))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____14157 = (

let uu____14162 = (

let uu____14163 = (

let uu____14171 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (uu____14171)))
in (FStar_SMTEncoding_Util.mkForall' uu____14163))
in ((uu____14162), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14157))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (uu____14128) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (uu____14090) with
| (decls, env) -> begin
(

let kindingAx = (

let uu____14195 = (encode_term_pred None res env' tapp)
in (match (uu____14195) with
| (k, decls) -> begin
(

let karr = (match (((FStar_List.length formals) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____14209 = (

let uu____14210 = (

let uu____14215 = (

let uu____14216 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____14216))
in ((uu____14215), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14210))
in (uu____14209)::[])
end
| uu____14219 -> begin
[]
end)
in (

let uu____14220 = (

let uu____14222 = (

let uu____14224 = (

let uu____14225 = (

let uu____14230 = (

let uu____14231 = (

let uu____14237 = (FStar_SMTEncoding_Util.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (uu____14237)))
in (FStar_SMTEncoding_Util.mkForall uu____14231))
in ((uu____14230), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14225))
in (uu____14224)::[])
in (FStar_List.append karr uu____14222))
in (FStar_List.append decls uu____14220)))
end))
in (

let aux = (

let uu____14247 = (

let uu____14249 = (inversion_axioms tapp vars)
in (

let uu____14251 = (

let uu____14253 = (pretype_axiom tapp vars)
in (uu____14253)::[])
in (FStar_List.append uu____14249 uu____14251)))
in (FStar_List.append kindingAx uu____14247))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14258, uu____14259, uu____14260, uu____14261, uu____14262, uu____14263, uu____14264) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14271, t, uu____14273, n_tps, quals, uu____14276, drange) -> begin
(

let uu____14282 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____14282) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____14293 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____14293) with
| (formals, t_res) -> begin
(

let uu____14315 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____14315) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____14324 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____14324) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (

let uu____14357 = (mk_term_projector_name d x)
in ((uu____14357), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (

let uu____14359 = (

let uu____14368 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (uu____14368), (true)))
in (FStar_All.pipe_right uu____14359 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____14388 = (encode_term_pred None t env ddtok_tm)
in (match (uu____14388) with
| (tok_typing, decls3) -> begin
(

let uu____14395 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____14395) with
| (vars', guards', env'', decls_formals, uu____14410) -> begin
(

let uu____14417 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (uu____14417) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____14436 -> begin
(

let uu____14440 = (

let uu____14441 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____14441))
in (uu____14440)::[])
end)
in (

let encode_elim = (fun uu____14448 -> (

let uu____14449 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____14449) with
| (head, args) -> begin
(

let uu____14478 = (

let uu____14479 = (FStar_Syntax_Subst.compress head)
in uu____14479.FStar_Syntax_Syntax.n)
in (match (uu____14478) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____14497 = (encode_args args env')
in (match (uu____14497) with
| (encoded_args, arg_decls) -> begin
(

let uu____14508 = (FStar_List.fold_left (fun uu____14519 arg -> (match (uu____14519) with
| (env, arg_vars, eqns) -> begin
(

let uu____14538 = (

let uu____14542 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env uu____14542))
in (match (uu____14538) with
| (uu____14548, xv, env) -> begin
(

let uu____14551 = (

let uu____14553 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____14553)::eqns)
in ((env), ((xv)::arg_vars), (uu____14551)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (uu____14508) with
| (uu____14561, arg_vars, eqns) -> begin
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

let uu____14582 = (

let uu____14587 = (

let uu____14588 = (

let uu____14594 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14600 = (

let uu____14601 = (

let uu____14604 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (uu____14604)))
in (FStar_SMTEncoding_Util.mkImp uu____14601))
in ((((ty_pred)::[])::[]), (uu____14594), (uu____14600))))
in (FStar_SMTEncoding_Util.mkForall uu____14588))
in ((uu____14587), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (uu____14582))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____14618 = (varops.fresh "x")
in ((uu____14618), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____14620 = (

let uu____14625 = (

let uu____14626 = (

let uu____14632 = (

let uu____14635 = (

let uu____14637 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in (uu____14637)::[])
in (uu____14635)::[])
in (

let uu____14640 = (

let uu____14641 = (

let uu____14644 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____14645 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in ((uu____14644), (uu____14645))))
in (FStar_SMTEncoding_Util.mkImp uu____14641))
in ((uu____14632), ((x)::[]), (uu____14640))))
in (FStar_SMTEncoding_Util.mkForall uu____14626))
in (

let uu____14655 = (

let uu____14657 = (varops.mk_unique "lextop")
in Some (uu____14657))
in ((uu____14625), (Some ("lextop is top")), (uu____14655))))
in FStar_SMTEncoding_Term.Assume (uu____14620))))
end
| uu____14660 -> begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(

let uu____14671 = (

let uu____14672 = (FStar_SMTEncoding_Util.mkFreeV v)
in (FStar_SMTEncoding_Util.mk_Precedes uu____14672 dapp))
in (uu____14671)::[])
end
| uu____14673 -> begin
(failwith "unexpected sort")
end))))
in (

let uu____14675 = (

let uu____14680 = (

let uu____14681 = (

let uu____14687 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14693 = (

let uu____14694 = (

let uu____14697 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____14697)))
in (FStar_SMTEncoding_Util.mkImp uu____14694))
in ((((ty_pred)::[])::[]), (uu____14687), (uu____14693))))
in (FStar_SMTEncoding_Util.mkForall uu____14681))
in ((uu____14680), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (uu____14675)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| uu____14708 -> begin
((

let uu____14710 = (

let uu____14711 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____14712 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____14711 uu____14712)))
in (FStar_Errors.warn drange uu____14710));
(([]), ([]));
)
end))
end)))
in (

let uu____14715 = (encode_elim ())
in (match (uu____14715) with
| (decls2, elim) -> begin
(

let g = (

let uu____14727 = (

let uu____14729 = (

let uu____14731 = (

let uu____14733 = (

let uu____14735 = (

let uu____14736 = (

let uu____14742 = (

let uu____14744 = (

let uu____14745 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____14745))
in Some (uu____14744))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____14742)))
in FStar_SMTEncoding_Term.DeclFun (uu____14736))
in (uu____14735)::[])
in (

let uu____14748 = (

let uu____14750 = (

let uu____14752 = (

let uu____14754 = (

let uu____14756 = (

let uu____14758 = (

let uu____14760 = (

let uu____14761 = (

let uu____14766 = (

let uu____14767 = (

let uu____14773 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____14773)))
in (FStar_SMTEncoding_Util.mkForall uu____14767))
in ((uu____14766), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (uu____14761))
in (

let uu____14781 = (

let uu____14783 = (

let uu____14784 = (

let uu____14789 = (

let uu____14790 = (

let uu____14796 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____14802 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____14796), (uu____14802))))
in (FStar_SMTEncoding_Util.mkForall uu____14790))
in ((uu____14789), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (uu____14784))
in (uu____14783)::[])
in (uu____14760)::uu____14781))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::uu____14758)
in (FStar_List.append uu____14756 elim))
in (FStar_List.append decls_pred uu____14754))
in (FStar_List.append decls_formals uu____14752))
in (FStar_List.append proxy_fresh uu____14750))
in (FStar_List.append uu____14733 uu____14748)))
in (FStar_List.append decls3 uu____14731))
in (FStar_List.append decls2 uu____14729))
in (FStar_List.append binder_decls uu____14727))
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
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____14825 se -> (match (uu____14825) with
| (g, env) -> begin
(

let uu____14837 = (encode_sigelt env se)
in (match (uu____14837) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____14873 -> (match (uu____14873) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____14891) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____14896 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____14896) with
| true -> begin
(

let uu____14897 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14898 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14899 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____14897 uu____14898 uu____14899))))
end
| uu____14900 -> begin
()
end));
(

let uu____14901 = (encode_term t1 env)
in (match (uu____14901) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____14911 = (

let uu____14915 = (

let uu____14916 = (

let uu____14917 = (FStar_Util.digest_of_string t_hash)
in (

let uu____14918 = (

let uu____14919 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____14919))
in (Prims.strcat uu____14917 uu____14918)))
in (Prims.strcat "x_" uu____14916))
in (new_term_constant_from_string env x uu____14915))
in (match (uu____14911) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = (

let uu____14930 = (FStar_Options.log_queries ())
in (match (uu____14930) with
| true -> begin
(

let uu____14932 = (

let uu____14933 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14934 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14935 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____14933 uu____14934 uu____14935))))
in Some (uu____14932))
end
| uu____14936 -> begin
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
| FStar_TypeChecker_Env.Binding_lid (x, (uu____14948, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____14957 = (encode_free_var env fv t t_norm [])
in (match (uu____14957) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let uu____14976 = (encode_sigelt env se)
in (match (uu____14976) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____14986 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____14986) with
| (uu____14998, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun uu____15043 -> (match (uu____15043) with
| (l, uu____15050, uu____15051) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____15072 -> (match (uu____15072) with
| (l, uu____15080, uu____15081) -> begin
(

let uu____15086 = (FStar_All.pipe_left (fun _0_39 -> FStar_SMTEncoding_Term.Echo (_0_39)) (Prims.fst l))
in (

let uu____15087 = (

let uu____15089 = (

let uu____15090 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____15090))
in (uu____15089)::[])
in (uu____15086)::uu____15087))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____15101 = (

let uu____15103 = (

let uu____15104 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____15104; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (uu____15103)::[])
in (FStar_ST.write last_env uu____15101)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (

let uu____15122 = (FStar_ST.read last_env)
in (match (uu____15122) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____15128 -> begin
(

let uu___156_15130 = e
in {bindings = uu___156_15130.bindings; depth = uu___156_15130.depth; tcenv = tcenv; warn = uu___156_15130.warn; cache = uu___156_15130.cache; nolabels = uu___156_15130.nolabels; use_zfuel_name = uu___156_15130.use_zfuel_name; encode_non_total_function_typ = uu___156_15130.encode_non_total_function_typ})
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____15134 = (FStar_ST.read last_env)
in (match (uu____15134) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____15139)::tl -> begin
(FStar_ST.write last_env ((env)::tl))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____15147 -> (

let uu____15148 = (FStar_ST.read last_env)
in (match (uu____15148) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd)::tl -> begin
(

let refs = (FStar_Util.smap_copy hd.cache)
in (

let top = (

let uu___157_15169 = hd
in {bindings = uu___157_15169.bindings; depth = uu___157_15169.depth; tcenv = uu___157_15169.tcenv; warn = uu___157_15169.warn; cache = refs; nolabels = uu___157_15169.nolabels; use_zfuel_name = uu___157_15169.use_zfuel_name; encode_non_total_function_typ = uu___157_15169.encode_non_total_function_typ})
in (FStar_ST.write last_env ((top)::(hd)::tl))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____15175 -> (

let uu____15176 = (FStar_ST.read last_env)
in (match (uu____15176) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____15181)::tl -> begin
(FStar_ST.write last_env tl)
end)))


let mark_env : Prims.unit  ->  Prims.unit = (fun uu____15189 -> (push_env ()))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15192 -> (pop_env ()))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15195 -> (

let uu____15196 = (FStar_ST.read last_env)
in (match (uu____15196) with
| (hd)::(uu____15202)::tl -> begin
(FStar_ST.write last_env ((hd)::tl))
end
| uu____15208 -> begin
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

let uu____15253 = (FStar_Options.log_queries ())
in (match (uu____15253) with
| true -> begin
(

let uu____15255 = (

let uu____15256 = (

let uu____15257 = (

let uu____15258 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____15258 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____15257))
in FStar_SMTEncoding_Term.Caption (uu____15256))
in (uu____15255)::decls)
end
| uu____15263 -> begin
decls
end)))
in (

let env = (get_env tcenv)
in (

let uu____15265 = (encode_sigelt env se)
in (match (uu____15265) with
| (decls, env) -> begin
((set_env env);
(

let uu____15271 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____15271));
)
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____15280 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____15282 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15282) with
| true -> begin
(

let uu____15283 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____15283))
end
| uu____15286 -> begin
()
end));
(

let env = (get_env tcenv)
in (

let uu____15288 = (encode_signature (

let uu___158_15292 = env
in {bindings = uu___158_15292.bindings; depth = uu___158_15292.depth; tcenv = uu___158_15292.tcenv; warn = false; cache = uu___158_15292.cache; nolabels = uu___158_15292.nolabels; use_zfuel_name = uu___158_15292.use_zfuel_name; encode_non_total_function_typ = uu___158_15292.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____15288) with
| (decls, env) -> begin
(

let caption = (fun decls -> (

let uu____15304 = (FStar_Options.log_queries ())
in (match (uu____15304) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____15307 -> begin
decls
end)))
in ((set_env (

let uu___159_15309 = env
in {bindings = uu___159_15309.bindings; depth = uu___159_15309.depth; tcenv = uu___159_15309.tcenv; warn = true; cache = uu___159_15309.cache; nolabels = uu___159_15309.nolabels; use_zfuel_name = uu___159_15309.use_zfuel_name; encode_non_total_function_typ = uu___159_15309.encode_non_total_function_typ}));
(

let uu____15311 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15311) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____15312 -> begin
()
end));
(

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls));
))
end)));
)))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____15346 = (

let uu____15347 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____15347.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____15346));
(

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____15355 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____15376 = (aux rest)
in (match (uu____15376) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let uu____15392 = (

let uu____15394 = (FStar_Syntax_Syntax.mk_binder (

let uu___160_15395 = x
in {FStar_Syntax_Syntax.ppname = uu___160_15395.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___160_15395.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (uu____15394)::out)
in ((uu____15392), (rest))))
end))
end
| uu____15398 -> begin
(([]), (bindings))
end))
in (

let uu____15402 = (aux bindings)
in (match (uu____15402) with
| (closing, bindings) -> begin
(

let uu____15416 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((uu____15416), (bindings)))
end)))
in (match (uu____15355) with
| (q, bindings) -> begin
(

let uu____15429 = (

let uu____15432 = (FStar_List.filter (fun uu___132_15434 -> (match (uu___132_15434) with
| FStar_TypeChecker_Env.Binding_sig (uu____15435) -> begin
false
end
| uu____15439 -> begin
true
end)) bindings)
in (encode_env_bindings env uu____15432))
in (match (uu____15429) with
| (env_decls, env) -> begin
((

let uu____15450 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____15450) with
| true -> begin
(

let uu____15451 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____15451))
end
| uu____15452 -> begin
()
end));
(

let uu____15453 = (encode_formula q env)
in (match (uu____15453) with
| (phi, qdecls) -> begin
(

let uu____15465 = (

let uu____15468 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____15468 phi))
in (match (uu____15465) with
| (labels, phi) -> begin
(

let uu____15478 = (encode_labels labels)
in (match (uu____15478) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____15499 = (

let uu____15504 = (FStar_SMTEncoding_Util.mkNot phi)
in (

let uu____15505 = (

let uu____15507 = (varops.mk_unique "@query")
in Some (uu____15507))
in ((uu____15504), (Some ("query")), (uu____15505))))
in FStar_SMTEncoding_Term.Assume (uu____15499))
in (

let suffix = (

let uu____15512 = (

let uu____15514 = (

let uu____15516 = (FStar_Options.print_z3_statistics ())
in (match (uu____15516) with
| true -> begin
(FStar_SMTEncoding_Term.PrintStats)::[]
end
| uu____15518 -> begin
[]
end))
in (FStar_List.append uu____15514 ((FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in (FStar_List.append label_suffix uu____15512))
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

let uu____15529 = (encode_formula q env)
in (match (uu____15529) with
| (f, uu____15533) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____15535) -> begin
true
end
| uu____15538 -> begin
false
end);
)
end));
)))





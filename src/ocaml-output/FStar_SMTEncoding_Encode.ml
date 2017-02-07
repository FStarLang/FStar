
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


let vargs = (fun args -> (FStar_List.filter (fun uu___109_74 -> (match (uu___109_74) with
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

let uu___134_140 = a
in (

let uu____141 = (FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____141; FStar_Syntax_Syntax.index = uu___134_140.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___134_140.FStar_Syntax_Syntax.sort}))
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

let uu___135_785 = x
in (

let uu____786 = (FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname)
in {FStar_Syntax_Syntax.ppname = uu____786; FStar_Syntax_Syntax.index = uu___135_785.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu___135_785.FStar_Syntax_Syntax.sort})))

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

let uu____950 = (FStar_All.pipe_right e.bindings (FStar_List.map (fun uu___110_954 -> (match (uu___110_954) with
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

let uu___136_1019 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = (env.depth + (Prims.parse_int "1")); tcenv = uu___136_1019.tcenv; warn = uu___136_1019.warn; cache = uu___136_1019.cache; nolabels = uu___136_1019.nolabels; use_zfuel_name = uu___136_1019.use_zfuel_name; encode_non_total_function_typ = uu___136_1019.encode_non_total_function_typ}))))))


let new_term_constant : env_t  ->  FStar_Syntax_Syntax.bv  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x -> (

let ysym = (varops.new_var x.FStar_Syntax_Syntax.ppname x.FStar_Syntax_Syntax.index)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___137_1032 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___137_1032.depth; tcenv = uu___137_1032.tcenv; warn = uu___137_1032.warn; cache = uu___137_1032.cache; nolabels = uu___137_1032.nolabels; use_zfuel_name = uu___137_1032.use_zfuel_name; encode_non_total_function_typ = uu___137_1032.encode_non_total_function_typ}))))))


let new_term_constant_from_string : env_t  ->  FStar_Syntax_Syntax.bv  ->  Prims.string  ->  (Prims.string * FStar_SMTEncoding_Term.term * env_t) = (fun env x str -> (

let ysym = (varops.mk_unique str)
in (

let y = (FStar_SMTEncoding_Util.mkApp ((ysym), ([])))
in ((ysym), (y), ((

let uu___138_1048 = env
in {bindings = (Binding_var (((x), (y))))::env.bindings; depth = uu___138_1048.depth; tcenv = uu___138_1048.tcenv; warn = uu___138_1048.warn; cache = uu___138_1048.cache; nolabels = uu___138_1048.nolabels; use_zfuel_name = uu___138_1048.use_zfuel_name; encode_non_total_function_typ = uu___138_1048.encode_non_total_function_typ}))))))


let push_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term  ->  env_t = (fun env x t -> (

let uu___139_1058 = env
in {bindings = (Binding_var (((x), (t))))::env.bindings; depth = uu___139_1058.depth; tcenv = uu___139_1058.tcenv; warn = uu___139_1058.warn; cache = uu___139_1058.cache; nolabels = uu___139_1058.nolabels; use_zfuel_name = uu___139_1058.use_zfuel_name; encode_non_total_function_typ = uu___139_1058.encode_non_total_function_typ}))


let lookup_term_var : env_t  ->  FStar_Syntax_Syntax.bv  ->  FStar_SMTEncoding_Term.term = (fun env a -> (

let aux = (fun a' -> (lookup_binding env (fun uu___111_1074 -> (match (uu___111_1074) with
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

let uu___140_1120 = env
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
in {bindings = uu____1121; depth = uu___140_1120.depth; tcenv = uu___140_1120.tcenv; warn = uu___140_1120.warn; cache = uu___140_1120.cache; nolabels = uu___140_1120.nolabels; use_zfuel_name = uu___140_1120.use_zfuel_name; encode_non_total_function_typ = uu___140_1120.encode_non_total_function_typ}))
in ((fname), (ftok), (uu____1119))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun uu___112_1155 -> (match (uu___112_1155) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| uu____1177 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (

let uu____1189 = (lookup_binding env (fun uu___113_1191 -> (match (uu___113_1191) with
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

let uu___141_1263 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = uu___141_1263.depth; tcenv = uu___141_1263.tcenv; warn = uu___141_1263.warn; cache = uu___141_1263.cache; nolabels = uu___141_1263.nolabels; use_zfuel_name = uu___141_1263.use_zfuel_name; encode_non_total_function_typ = uu___141_1263.encode_non_total_function_typ}))


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

let uu___142_1298 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = uu___142_1298.depth; tcenv = uu___142_1298.tcenv; warn = uu___142_1298.warn; cache = uu___142_1298.cache; nolabels = uu___142_1298.nolabels; use_zfuel_name = uu___142_1298.use_zfuel_name; encode_non_total_function_typ = uu___142_1298.encode_non_total_function_typ}))
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


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___114_1476 -> (match (uu___114_1476) with
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
(((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___115_1661 -> (match (uu___115_1661) with
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
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


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


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___116_1769 -> (match (uu___116_1769) with
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


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun uu___117_1926 -> (match (uu___117_1926) with
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

let uu___143_2516 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___143_2516.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___143_2516.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___143_2516.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___143_2516.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___143_2516.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___143_2516.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___143_2516.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___143_2516.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___143_2516.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___143_2516.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___143_2516.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___143_2516.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___143_2516.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___143_2516.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___143_2516.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___143_2516.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___143_2516.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___143_2516.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___143_2516.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___143_2516.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___143_2516.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___143_2516.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___143_2516.FStar_TypeChecker_Env.qname_and_index}) res)
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

let is_impure = (fun uu___118_3924 -> (match (uu___118_3924) with
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

let tc_name = (FStar_TypeChecker_Env.typ_of_datacon env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____4691 = (FStar_TypeChecker_Env.datacons_of_typ env.tcenv tc_name)
in (match (uu____4691) with
| (uu____4695, (uu____4696)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____4698 -> begin
(

let is_f = (mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4720 -> (match (uu____4720) with
| (arg, uu____4726) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____4736 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____4736)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end)))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4755) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____4770) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____4785 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4807 -> (match (uu____4807) with
| (arg, uu____4816) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____4826 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____4826)))
end))))
in (FStar_All.pipe_right uu____4785 FStar_List.flatten))
end))
in (

let pat_term = (fun uu____4842 -> (encode_term pat_term env))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____4849 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____4864 uu____4865 -> (match (((uu____4864), (uu____4865))) with
| ((tms, decls), (t, uu____4885)) -> begin
(

let uu____4896 = (encode_term t env)
in (match (uu____4896) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____4849) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let list_elements = (fun e -> (

let uu____4934 = (FStar_Syntax_Util.list_elements e)
in (match (uu____4934) with
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

let uu____4952 = (

let uu____4962 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____4962 FStar_Syntax_Util.head_and_args))
in (match (uu____4952) with
| (head, args) -> begin
(

let uu____4993 = (

let uu____5001 = (

let uu____5002 = (FStar_Syntax_Util.un_uinst head)
in uu____5002.FStar_Syntax_Syntax.n)
in ((uu____5001), (args)))
in (match (uu____4993) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____5016, uu____5017))::((e, uu____5019))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5050))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| uu____5071 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let uu____5104 = (

let uu____5114 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right uu____5114 FStar_Syntax_Util.head_and_args))
in (match (uu____5104) with
| (head, args) -> begin
(

let uu____5143 = (

let uu____5151 = (

let uu____5152 = (FStar_Syntax_Util.un_uinst head)
in uu____5152.FStar_Syntax_Syntax.n)
in ((uu____5151), (args)))
in (match (uu____5143) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5165))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| uu____5185 -> begin
None
end))
end)))
in (match (elts) with
| (t)::[] -> begin
(

let uu____5203 = (smt_pat_or t)
in (match (uu____5203) with
| Some (e) -> begin
(

let uu____5219 = (list_elements e)
in (FStar_All.pipe_right uu____5219 (FStar_List.map (fun branch -> (

let uu____5236 = (list_elements branch)
in (FStar_All.pipe_right uu____5236 (FStar_List.map one_pat)))))))
end
| uu____5250 -> begin
(

let uu____5254 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5254)::[])
end))
end
| uu____5285 -> begin
(

let uu____5287 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5287)::[])
end))))
in (

let uu____5318 = (

let uu____5334 = (

let uu____5335 = (FStar_Syntax_Subst.compress t)
in uu____5335.FStar_Syntax_Syntax.n)
in (match (uu____5334) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____5365 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____5365) with
| (binders, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____5400; FStar_Syntax_Syntax.effect_name = uu____5401; FStar_Syntax_Syntax.result_typ = uu____5402; FStar_Syntax_Syntax.effect_args = ((pre, uu____5404))::((post, uu____5406))::((pats, uu____5408))::[]; FStar_Syntax_Syntax.flags = uu____5409}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (

let uu____5443 = (lemma_pats pats')
in ((binders), (pre), (post), (uu____5443))))
end
| uu____5462 -> begin
(failwith "impos")
end)
end))
end
| uu____5478 -> begin
(failwith "Impos")
end))
in (match (uu____5318) with
| (binders, pre, post, patterns) -> begin
(

let uu____5522 = (encode_binders None binders env)
in (match (uu____5522) with
| (vars, guards, env, decls, uu____5537) -> begin
(

let uu____5544 = (

let uu____5551 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let uu____5582 = (

let uu____5587 = (FStar_All.pipe_right branch (FStar_List.map (fun uu____5603 -> (match (uu____5603) with
| (t, uu____5610) -> begin
(encode_term t (

let uu___144_5613 = env
in {bindings = uu___144_5613.bindings; depth = uu___144_5613.depth; tcenv = uu___144_5613.tcenv; warn = uu___144_5613.warn; cache = uu___144_5613.cache; nolabels = uu___144_5613.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___144_5613.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right uu____5587 FStar_List.unzip))
in (match (uu____5582) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right uu____5551 FStar_List.unzip))
in (match (uu____5544) with
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

let uu____5677 = (

let uu____5678 = (FStar_SMTEncoding_Util.mkFreeV l)
in (FStar_SMTEncoding_Util.mk_Precedes uu____5678 e))
in (uu____5677)::p))))
end
| uu____5679 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (

let uu____5708 = (FStar_SMTEncoding_Util.mk_Precedes tl e)
in (uu____5708)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(

let uu____5716 = (

let uu____5717 = (FStar_SMTEncoding_Util.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mk_LexCons uu____5717 tl))
in (aux uu____5716 vars))
end
| uu____5718 -> begin
pats
end))
in (

let uu____5722 = (FStar_SMTEncoding_Util.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux uu____5722 vars)))
end)
end)
in (

let env = (

let uu___145_5724 = env
in {bindings = uu___145_5724.bindings; depth = uu___145_5724.depth; tcenv = uu___145_5724.tcenv; warn = uu___145_5724.warn; cache = uu___145_5724.cache; nolabels = true; use_zfuel_name = uu___145_5724.use_zfuel_name; encode_non_total_function_typ = uu___145_5724.encode_non_total_function_typ})
in (

let uu____5725 = (

let uu____5728 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____5728 env))
in (match (uu____5725) with
| (pre, decls'') -> begin
(

let uu____5733 = (

let uu____5736 = (FStar_Syntax_Util.unmeta post)
in (encode_formula uu____5736 env))
in (match (uu____5733) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (

let uu____5743 = (

let uu____5744 = (

let uu____5750 = (

let uu____5751 = (

let uu____5754 = (FStar_SMTEncoding_Util.mk_and_l ((pre)::guards))
in ((uu____5754), (post)))
in (FStar_SMTEncoding_Util.mkImp uu____5751))
in ((pats), (vars), (uu____5750)))
in (FStar_SMTEncoding_Util.mkForall uu____5744))
in ((uu____5743), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> (

let uu____5767 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____5767) with
| true -> begin
(

let uu____5768 = (FStar_Syntax_Print.tag_of_term phi)
in (

let uu____5769 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____5768 uu____5769)))
end
| uu____5770 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____5796 = (FStar_Util.fold_map (fun decls x -> (

let uu____5809 = (encode_term (Prims.fst x) env)
in (match (uu____5809) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____5796) with
| (decls, args) -> begin
(

let uu____5826 = (

let uu___146_5827 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___146_5827.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___146_5827.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____5826), (decls)))
end)))
in (

let const_op = (fun f r uu____5846 -> (

let uu____5849 = (f r)
in ((uu____5849), ([]))))
in (

let un_op = (fun f l -> (

let uu____5865 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____5865)))
in (

let bin_op = (fun f uu___119_5878 -> (match (uu___119_5878) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____5886 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____5913 = (FStar_Util.fold_map (fun decls uu____5922 -> (match (uu____5922) with
| (t, uu____5930) -> begin
(

let uu____5931 = (encode_formula t env)
in (match (uu____5931) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (uu____5913) with
| (decls, phis) -> begin
(

let uu____5948 = (

let uu___147_5949 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___147_5949.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___147_5949.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____5948), (decls)))
end)))
in (

let eq_op = (fun r uu___120_5965 -> (match (uu___120_5965) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(

let uu____6025 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____6025 r ((e1)::(e2)::[])))
end
| l -> begin
(

let uu____6045 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____6045 r l))
end))
in (

let mk_imp = (fun r uu___121_6064 -> (match (uu___121_6064) with
| ((lhs, uu____6068))::((rhs, uu____6070))::[] -> begin
(

let uu____6091 = (encode_formula rhs env)
in (match (uu____6091) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____6100) -> begin
((l1), (decls1))
end
| uu____6103 -> begin
(

let uu____6104 = (encode_formula lhs env)
in (match (uu____6104) with
| (l2, decls2) -> begin
(

let uu____6111 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____6111), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____6113 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___122_6128 -> (match (uu___122_6128) with
| ((guard, uu____6132))::((_then, uu____6134))::((_else, uu____6136))::[] -> begin
(

let uu____6165 = (encode_formula guard env)
in (match (uu____6165) with
| (g, decls1) -> begin
(

let uu____6172 = (encode_formula _then env)
in (match (uu____6172) with
| (t, decls2) -> begin
(

let uu____6179 = (encode_formula _else env)
in (match (uu____6179) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____6188 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____6207 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____6207)))
in (

let connectives = (

let uu____6219 = (

let uu____6228 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Syntax_Const.and_lid), (uu____6228)))
in (

let uu____6241 = (

let uu____6251 = (

let uu____6260 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Syntax_Const.or_lid), (uu____6260)))
in (

let uu____6273 = (

let uu____6283 = (

let uu____6293 = (

let uu____6302 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Syntax_Const.iff_lid), (uu____6302)))
in (

let uu____6315 = (

let uu____6325 = (

let uu____6335 = (

let uu____6344 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Syntax_Const.not_lid), (uu____6344)))
in (uu____6335)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::uu____6325)
in (uu____6293)::uu____6315))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::uu____6283)
in (uu____6251)::uu____6273))
in (uu____6219)::uu____6241))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____6506 = (encode_formula phi' env)
in (match (uu____6506) with
| (phi, decls) -> begin
(

let uu____6513 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))) r)
in ((uu____6513), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____6514) -> begin
(

let uu____6519 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula uu____6519 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____6548 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____6548) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____6556; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____6558; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____6574 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____6574) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____6606)::((x, uu____6608))::((t, uu____6610))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let uu____6644 = (encode_term x env)
in (match (uu____6644) with
| (x, decls) -> begin
(

let uu____6651 = (encode_term t env)
in (match (uu____6651) with
| (t, decls') -> begin
(

let uu____6658 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((uu____6658), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____6662))::((msg, uu____6664))::((phi, uu____6666))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(

let uu____6700 = (

let uu____6703 = (

let uu____6704 = (FStar_Syntax_Subst.compress r)
in uu____6704.FStar_Syntax_Syntax.n)
in (

let uu____6707 = (

let uu____6708 = (FStar_Syntax_Subst.compress msg)
in uu____6708.FStar_Syntax_Syntax.n)
in ((uu____6703), (uu____6707))))
in (match (uu____6700) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____6715))) -> begin
(

let phi = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false)))))))) None r)
in (fallback phi))
end
| uu____6731 -> begin
(fallback phi)
end))
end
| uu____6734 when (head_redex env head) -> begin
(

let uu____6742 = (whnf env phi)
in (encode_formula uu____6742 env))
end
| uu____6743 -> begin
(

let uu____6751 = (encode_term phi env)
in (match (uu____6751) with
| (tt, decls) -> begin
(

let uu____6758 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___148_6759 = tt
in {FStar_SMTEncoding_Term.tm = uu___148_6759.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___148_6759.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((uu____6758), (decls)))
end))
end))
end
| uu____6762 -> begin
(

let uu____6763 = (encode_term phi env)
in (match (uu____6763) with
| (tt, decls) -> begin
(

let uu____6770 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___149_6771 = tt
in {FStar_SMTEncoding_Term.tm = uu___149_6771.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___149_6771.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((uu____6770), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let uu____6798 = (encode_binders None bs env)
in (match (uu____6798) with
| (vars, guards, env, decls, uu____6820) -> begin
(

let uu____6827 = (

let uu____6834 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____6857 = (

let uu____6862 = (FStar_All.pipe_right p (FStar_List.map (fun uu____6876 -> (match (uu____6876) with
| (t, uu____6882) -> begin
(encode_term t (

let uu___150_6883 = env
in {bindings = uu___150_6883.bindings; depth = uu___150_6883.depth; tcenv = uu___150_6883.tcenv; warn = uu___150_6883.warn; cache = uu___150_6883.cache; nolabels = uu___150_6883.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___150_6883.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right uu____6862 FStar_List.unzip))
in (match (uu____6857) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right uu____6834 FStar_List.unzip))
in (match (uu____6827) with
| (pats, decls') -> begin
(

let uu____6935 = (encode_formula body env)
in (match (uu____6935) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____6954; FStar_SMTEncoding_Term.rng = uu____6955})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| uu____6963 -> begin
guards
end)
in (

let uu____6966 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((vars), (pats), (uu____6966), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug phi);
(

let phi = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun uu____7000 -> (match (uu____7000) with
| (x, uu____7004) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats) with
| [] -> begin
()
end
| (hd)::tl -> begin
(

let pat_vars = (

let uu____7010 = (FStar_Syntax_Free.names hd)
in (FStar_List.fold_left (fun out x -> (

let uu____7016 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____7016))) uu____7010 tl))
in (

let uu____7018 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____7030 -> (match (uu____7030) with
| (b, uu____7034) -> begin
(

let uu____7035 = (FStar_Util.set_mem b pat_vars)
in (not (uu____7035)))
end))))
in (match (uu____7018) with
| None -> begin
()
end
| Some (x, uu____7039) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd.FStar_Syntax_Syntax.pos tl)
in (

let uu____7049 = (

let uu____7050 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____7050))
in (FStar_Errors.warn pos uu____7049)))
end)))
end)))
in (

let uu____7051 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____7051) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____7057 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____7093 -> (match (uu____7093) with
| (l, uu____7103) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____7057) with
| None -> begin
(fallback phi)
end
| Some (uu____7126, f) -> begin
(f phi.FStar_Syntax_Syntax.pos arms)
end))
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7155 = (encode_q_body env vars pats body)
in (match (uu____7155) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (

let uu____7181 = (

let uu____7187 = (FStar_SMTEncoding_Util.mkImp ((guard), (body)))
in ((pats), (vars), (uu____7187)))
in (FStar_SMTEncoding_Term.mkForall uu____7181 phi.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7199 = (encode_q_body env vars pats body)
in (match (uu____7199) with
| (vars, pats, guard, body, decls) -> begin
(

let uu____7224 = (

let uu____7225 = (

let uu____7231 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body)))
in ((pats), (vars), (uu____7231)))
in (FStar_SMTEncoding_Term.mkExists uu____7225 phi.FStar_Syntax_Syntax.pos))
in ((uu____7224), (decls)))
end));
)
end))));
)))))))))))))))

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let prims : prims_t = (

let uu____7280 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7280) with
| (asym, a) -> begin
(

let uu____7285 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7285) with
| (xsym, x) -> begin
(

let uu____7290 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7290) with
| (ysym, y) -> begin
(

let quant = (fun vars body x -> (

let xname_decl = (

let uu____7320 = (

let uu____7326 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (uu____7326), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____7320))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (

let uu____7341 = (

let uu____7345 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x), (uu____7345)))
in (FStar_SMTEncoding_Util.mkApp uu____7341))
in (

let xtok = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (

let uu____7353 = (

let uu____7355 = (

let uu____7357 = (

let uu____7359 = (

let uu____7360 = (

let uu____7365 = (

let uu____7366 = (

let uu____7372 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____7372)))
in (FStar_SMTEncoding_Util.mkForall uu____7366))
in ((uu____7365), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (uu____7360))
in (

let uu____7382 = (

let uu____7384 = (

let uu____7385 = (

let uu____7390 = (

let uu____7391 = (

let uu____7397 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____7397)))
in (FStar_SMTEncoding_Util.mkForall uu____7391))
in ((uu____7390), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x)))))
in FStar_SMTEncoding_Term.Assume (uu____7385))
in (uu____7384)::[])
in (uu____7359)::uu____7382))
in (xtok_decl)::uu____7357)
in (xname_decl)::uu____7355)
in ((xtok), (uu____7353))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (

let uu____7447 = (

let uu____7455 = (

let uu____7461 = (

let uu____7462 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7462))
in (quant axy uu____7461))
in ((FStar_Syntax_Const.op_Eq), (uu____7455)))
in (

let uu____7468 = (

let uu____7477 = (

let uu____7485 = (

let uu____7491 = (

let uu____7492 = (

let uu____7493 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____7493))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7492))
in (quant axy uu____7491))
in ((FStar_Syntax_Const.op_notEq), (uu____7485)))
in (

let uu____7499 = (

let uu____7508 = (

let uu____7516 = (

let uu____7522 = (

let uu____7523 = (

let uu____7524 = (

let uu____7527 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7528 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7527), (uu____7528))))
in (FStar_SMTEncoding_Util.mkLT uu____7524))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7523))
in (quant xy uu____7522))
in ((FStar_Syntax_Const.op_LT), (uu____7516)))
in (

let uu____7534 = (

let uu____7543 = (

let uu____7551 = (

let uu____7557 = (

let uu____7558 = (

let uu____7559 = (

let uu____7562 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7563 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7562), (uu____7563))))
in (FStar_SMTEncoding_Util.mkLTE uu____7559))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7558))
in (quant xy uu____7557))
in ((FStar_Syntax_Const.op_LTE), (uu____7551)))
in (

let uu____7569 = (

let uu____7578 = (

let uu____7586 = (

let uu____7592 = (

let uu____7593 = (

let uu____7594 = (

let uu____7597 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7598 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7597), (uu____7598))))
in (FStar_SMTEncoding_Util.mkGT uu____7594))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7593))
in (quant xy uu____7592))
in ((FStar_Syntax_Const.op_GT), (uu____7586)))
in (

let uu____7604 = (

let uu____7613 = (

let uu____7621 = (

let uu____7627 = (

let uu____7628 = (

let uu____7629 = (

let uu____7632 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7633 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7632), (uu____7633))))
in (FStar_SMTEncoding_Util.mkGTE uu____7629))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7628))
in (quant xy uu____7627))
in ((FStar_Syntax_Const.op_GTE), (uu____7621)))
in (

let uu____7639 = (

let uu____7648 = (

let uu____7656 = (

let uu____7662 = (

let uu____7663 = (

let uu____7664 = (

let uu____7667 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7668 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7667), (uu____7668))))
in (FStar_SMTEncoding_Util.mkSub uu____7664))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7663))
in (quant xy uu____7662))
in ((FStar_Syntax_Const.op_Subtraction), (uu____7656)))
in (

let uu____7674 = (

let uu____7683 = (

let uu____7691 = (

let uu____7697 = (

let uu____7698 = (

let uu____7699 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____7699))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7698))
in (quant qx uu____7697))
in ((FStar_Syntax_Const.op_Minus), (uu____7691)))
in (

let uu____7705 = (

let uu____7714 = (

let uu____7722 = (

let uu____7728 = (

let uu____7729 = (

let uu____7730 = (

let uu____7733 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7734 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7733), (uu____7734))))
in (FStar_SMTEncoding_Util.mkAdd uu____7730))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7729))
in (quant xy uu____7728))
in ((FStar_Syntax_Const.op_Addition), (uu____7722)))
in (

let uu____7740 = (

let uu____7749 = (

let uu____7757 = (

let uu____7763 = (

let uu____7764 = (

let uu____7765 = (

let uu____7768 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7769 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7768), (uu____7769))))
in (FStar_SMTEncoding_Util.mkMul uu____7765))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7764))
in (quant xy uu____7763))
in ((FStar_Syntax_Const.op_Multiply), (uu____7757)))
in (

let uu____7775 = (

let uu____7784 = (

let uu____7792 = (

let uu____7798 = (

let uu____7799 = (

let uu____7800 = (

let uu____7803 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7804 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7803), (uu____7804))))
in (FStar_SMTEncoding_Util.mkDiv uu____7800))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7799))
in (quant xy uu____7798))
in ((FStar_Syntax_Const.op_Division), (uu____7792)))
in (

let uu____7810 = (

let uu____7819 = (

let uu____7827 = (

let uu____7833 = (

let uu____7834 = (

let uu____7835 = (

let uu____7838 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7839 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7838), (uu____7839))))
in (FStar_SMTEncoding_Util.mkMod uu____7835))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7834))
in (quant xy uu____7833))
in ((FStar_Syntax_Const.op_Modulus), (uu____7827)))
in (

let uu____7845 = (

let uu____7854 = (

let uu____7862 = (

let uu____7868 = (

let uu____7869 = (

let uu____7870 = (

let uu____7873 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____7874 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____7873), (uu____7874))))
in (FStar_SMTEncoding_Util.mkAnd uu____7870))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7869))
in (quant xy uu____7868))
in ((FStar_Syntax_Const.op_And), (uu____7862)))
in (

let uu____7880 = (

let uu____7889 = (

let uu____7897 = (

let uu____7903 = (

let uu____7904 = (

let uu____7905 = (

let uu____7908 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____7909 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____7908), (uu____7909))))
in (FStar_SMTEncoding_Util.mkOr uu____7905))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7904))
in (quant xy uu____7903))
in ((FStar_Syntax_Const.op_Or), (uu____7897)))
in (

let uu____7915 = (

let uu____7924 = (

let uu____7932 = (

let uu____7938 = (

let uu____7939 = (

let uu____7940 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____7940))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7939))
in (quant qx uu____7938))
in ((FStar_Syntax_Const.op_Negation), (uu____7932)))
in (uu____7924)::[])
in (uu____7889)::uu____7915))
in (uu____7854)::uu____7880))
in (uu____7819)::uu____7845))
in (uu____7784)::uu____7810))
in (uu____7749)::uu____7775))
in (uu____7714)::uu____7740))
in (uu____7683)::uu____7705))
in (uu____7648)::uu____7674))
in (uu____7613)::uu____7639))
in (uu____7578)::uu____7604))
in (uu____7543)::uu____7569))
in (uu____7508)::uu____7534))
in (uu____7477)::uu____7499))
in (uu____7447)::uu____7468))
in (

let mk = (fun l v -> (

let uu____8068 = (

let uu____8073 = (FStar_All.pipe_right prims (FStar_List.find (fun uu____8105 -> (match (uu____8105) with
| (l', uu____8114) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____8073 (FStar_Option.map (fun uu____8147 -> (match (uu____8147) with
| (uu____8158, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right uu____8068 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun uu____8199 -> (match (uu____8199) with
| (l', uu____8208) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let uu____8231 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____8231) with
| (xxsym, xx) -> begin
(

let uu____8236 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____8236) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let uu____8243 = (

let uu____8248 = (

let uu____8249 = (

let uu____8255 = (

let uu____8256 = (

let uu____8259 = (

let uu____8260 = (

let uu____8263 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____8263)))
in (FStar_SMTEncoding_Util.mkEq uu____8260))
in ((xx_has_type), (uu____8259)))
in (FStar_SMTEncoding_Util.mkImp uu____8256))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____8255)))
in (FStar_SMTEncoding_Util.mkForall uu____8249))
in (

let uu____8276 = (

let uu____8278 = (

let uu____8279 = (

let uu____8280 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "pretyping_" uu____8280))
in (varops.mk_unique uu____8279))
in Some (uu____8278))
in ((uu____8248), (Some ("pretyping")), (uu____8276))))
in FStar_SMTEncoding_Term.Assume (uu____8243))))
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

let uu____8311 = (

let uu____8312 = (

let uu____8317 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____8317), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8312))
in (

let uu____8320 = (

let uu____8322 = (

let uu____8323 = (

let uu____8328 = (

let uu____8329 = (

let uu____8335 = (

let uu____8336 = (

let uu____8339 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____8339)))
in (FStar_SMTEncoding_Util.mkImp uu____8336))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8335)))
in (mkForall_fuel uu____8329))
in ((uu____8328), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8323))
in (uu____8322)::[])
in (uu____8311)::uu____8320))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8368 = (

let uu____8369 = (

let uu____8374 = (

let uu____8375 = (

let uu____8381 = (

let uu____8384 = (

let uu____8386 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____8386)::[])
in (uu____8384)::[])
in (

let uu____8389 = (

let uu____8390 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8390 tt))
in ((uu____8381), ((bb)::[]), (uu____8389))))
in (FStar_SMTEncoding_Util.mkForall uu____8375))
in ((uu____8374), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8369))
in (

let uu____8402 = (

let uu____8404 = (

let uu____8405 = (

let uu____8410 = (

let uu____8411 = (

let uu____8417 = (

let uu____8418 = (

let uu____8421 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (uu____8421)))
in (FStar_SMTEncoding_Util.mkImp uu____8418))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8417)))
in (mkForall_fuel uu____8411))
in ((uu____8410), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8405))
in (uu____8404)::[])
in (uu____8368)::uu____8402))))))
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

let uu____8456 = (

let uu____8457 = (

let uu____8461 = (

let uu____8463 = (

let uu____8465 = (

let uu____8467 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____8468 = (

let uu____8470 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8470)::[])
in (uu____8467)::uu____8468))
in (tt)::uu____8465)
in (tt)::uu____8463)
in (("Prims.Precedes"), (uu____8461)))
in (FStar_SMTEncoding_Util.mkApp uu____8457))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8456))
in (

let precedes_y_x = (

let uu____8473 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8473))
in (

let uu____8475 = (

let uu____8476 = (

let uu____8481 = (

let uu____8482 = (

let uu____8488 = (

let uu____8491 = (

let uu____8493 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8493)::[])
in (uu____8491)::[])
in (

let uu____8496 = (

let uu____8497 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8497 tt))
in ((uu____8488), ((bb)::[]), (uu____8496))))
in (FStar_SMTEncoding_Util.mkForall uu____8482))
in ((uu____8481), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8476))
in (

let uu____8509 = (

let uu____8511 = (

let uu____8512 = (

let uu____8517 = (

let uu____8518 = (

let uu____8524 = (

let uu____8525 = (

let uu____8528 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (uu____8528)))
in (FStar_SMTEncoding_Util.mkImp uu____8525))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8524)))
in (mkForall_fuel uu____8518))
in ((uu____8517), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8512))
in (

let uu____8542 = (

let uu____8544 = (

let uu____8545 = (

let uu____8550 = (

let uu____8551 = (

let uu____8557 = (

let uu____8558 = (

let uu____8561 = (

let uu____8562 = (

let uu____8564 = (

let uu____8566 = (

let uu____8568 = (

let uu____8569 = (

let uu____8572 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____8573 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8572), (uu____8573))))
in (FStar_SMTEncoding_Util.mkGT uu____8569))
in (

let uu____8574 = (

let uu____8576 = (

let uu____8577 = (

let uu____8580 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8581 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8580), (uu____8581))))
in (FStar_SMTEncoding_Util.mkGTE uu____8577))
in (

let uu____8582 = (

let uu____8584 = (

let uu____8585 = (

let uu____8588 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8589 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____8588), (uu____8589))))
in (FStar_SMTEncoding_Util.mkLT uu____8585))
in (uu____8584)::[])
in (uu____8576)::uu____8582))
in (uu____8568)::uu____8574))
in (typing_pred_y)::uu____8566)
in (typing_pred)::uu____8564)
in (FStar_SMTEncoding_Util.mk_and_l uu____8562))
in ((uu____8561), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____8558))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____8557)))
in (mkForall_fuel uu____8551))
in ((uu____8550), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (uu____8545))
in (uu____8544)::[])
in (uu____8511)::uu____8542))
in (uu____8475)::uu____8509)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8620 = (

let uu____8621 = (

let uu____8626 = (

let uu____8627 = (

let uu____8633 = (

let uu____8636 = (

let uu____8638 = (FStar_SMTEncoding_Term.boxString b)
in (uu____8638)::[])
in (uu____8636)::[])
in (

let uu____8641 = (

let uu____8642 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8642 tt))
in ((uu____8633), ((bb)::[]), (uu____8641))))
in (FStar_SMTEncoding_Util.mkForall uu____8627))
in ((uu____8626), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8621))
in (

let uu____8654 = (

let uu____8656 = (

let uu____8657 = (

let uu____8662 = (

let uu____8663 = (

let uu____8669 = (

let uu____8670 = (

let uu____8673 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (uu____8673)))
in (FStar_SMTEncoding_Util.mkImp uu____8670))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8669)))
in (mkForall_fuel uu____8663))
in ((uu____8662), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8657))
in (uu____8656)::[])
in (uu____8620)::uu____8654))))))
in (

let mk_ref = (fun env reft_name uu____8696 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (

let uu____8707 = (

let uu____8711 = (

let uu____8713 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (uu____8713)::[])
in ((reft_name), (uu____8711)))
in (FStar_SMTEncoding_Util.mkApp uu____8707))
in (

let refb = (

let uu____8716 = (

let uu____8720 = (

let uu____8722 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (uu____8722)::[])
in ((reft_name), (uu____8720)))
in (FStar_SMTEncoding_Util.mkApp uu____8716))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (

let uu____8726 = (

let uu____8727 = (

let uu____8732 = (

let uu____8733 = (

let uu____8739 = (

let uu____8740 = (

let uu____8743 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (uu____8743)))
in (FStar_SMTEncoding_Util.mkImp uu____8740))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (uu____8739)))
in (mkForall_fuel uu____8733))
in ((uu____8732), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8727))
in (

let uu____8759 = (

let uu____8761 = (

let uu____8762 = (

let uu____8767 = (

let uu____8768 = (

let uu____8774 = (

let uu____8775 = (

let uu____8778 = (FStar_SMTEncoding_Util.mkAnd ((typing_pred), (typing_pred_b)))
in (

let uu____8779 = (

let uu____8780 = (

let uu____8783 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let uu____8784 = (FStar_SMTEncoding_Util.mkFreeV bb)
in ((uu____8783), (uu____8784))))
in (FStar_SMTEncoding_Util.mkEq uu____8780))
in ((uu____8778), (uu____8779))))
in (FStar_SMTEncoding_Util.mkImp uu____8775))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (uu____8774)))
in (mkForall_fuel' (Prims.parse_int "2") uu____8768))
in ((uu____8767), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (uu____8762))
in (uu____8761)::[])
in (uu____8726)::uu____8759))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), (Some ("true_interp")))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____8828 = (

let uu____8829 = (

let uu____8834 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____8834), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8829))
in (uu____8828)::[])))
in (

let mk_and_interp = (fun env conj uu____8846 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____8856 = (

let uu____8860 = (

let uu____8862 = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (uu____8862)::[])
in (("Valid"), (uu____8860)))
in (FStar_SMTEncoding_Util.mkApp uu____8856))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____8869 = (

let uu____8870 = (

let uu____8875 = (

let uu____8876 = (

let uu____8882 = (

let uu____8883 = (

let uu____8886 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____8886), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____8883))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____8882)))
in (FStar_SMTEncoding_Util.mkForall uu____8876))
in ((uu____8875), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8870))
in (uu____8869)::[])))))))))
in (

let mk_or_interp = (fun env disj uu____8911 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____8921 = (

let uu____8925 = (

let uu____8927 = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (uu____8927)::[])
in (("Valid"), (uu____8925)))
in (FStar_SMTEncoding_Util.mkApp uu____8921))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____8934 = (

let uu____8935 = (

let uu____8940 = (

let uu____8941 = (

let uu____8947 = (

let uu____8948 = (

let uu____8951 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____8951), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____8948))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____8947)))
in (FStar_SMTEncoding_Util.mkForall uu____8941))
in ((uu____8940), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8935))
in (uu____8934)::[])))))))))
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

let uu____8990 = (

let uu____8994 = (

let uu____8996 = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (uu____8996)::[])
in (("Valid"), (uu____8994)))
in (FStar_SMTEncoding_Util.mkApp uu____8990))
in (

let uu____8999 = (

let uu____9000 = (

let uu____9005 = (

let uu____9006 = (

let uu____9012 = (

let uu____9013 = (

let uu____9016 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((uu____9016), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9013))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (uu____9012)))
in (FStar_SMTEncoding_Util.mkForall uu____9006))
in ((uu____9005), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9000))
in (uu____8999)::[])))))))))
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

let uu____9061 = (

let uu____9065 = (

let uu____9067 = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (uu____9067)::[])
in (("Valid"), (uu____9065)))
in (FStar_SMTEncoding_Util.mkApp uu____9061))
in (

let uu____9070 = (

let uu____9071 = (

let uu____9076 = (

let uu____9077 = (

let uu____9083 = (

let uu____9084 = (

let uu____9087 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((uu____9087), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9084))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (uu____9083)))
in (FStar_SMTEncoding_Util.mkForall uu____9077))
in ((uu____9076), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9071))
in (uu____9070)::[])))))))))))
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

let uu____9126 = (

let uu____9130 = (

let uu____9132 = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (uu____9132)::[])
in (("Valid"), (uu____9130)))
in (FStar_SMTEncoding_Util.mkApp uu____9126))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9139 = (

let uu____9140 = (

let uu____9145 = (

let uu____9146 = (

let uu____9152 = (

let uu____9153 = (

let uu____9156 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____9156), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9153))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9152)))
in (FStar_SMTEncoding_Util.mkForall uu____9146))
in ((uu____9145), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9140))
in (uu____9139)::[])))))))))
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

let uu____9191 = (

let uu____9195 = (

let uu____9197 = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (uu____9197)::[])
in (("Valid"), (uu____9195)))
in (FStar_SMTEncoding_Util.mkApp uu____9191))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9204 = (

let uu____9205 = (

let uu____9210 = (

let uu____9211 = (

let uu____9217 = (

let uu____9218 = (

let uu____9221 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____9221), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9218))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9217)))
in (FStar_SMTEncoding_Util.mkForall uu____9211))
in ((uu____9210), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9205))
in (uu____9204)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let valid = (

let uu____9252 = (

let uu____9256 = (

let uu____9258 = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (uu____9258)::[])
in (("Valid"), (uu____9256)))
in (FStar_SMTEncoding_Util.mkApp uu____9252))
in (

let not_valid_a = (

let uu____9262 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9262))
in (

let uu____9264 = (

let uu____9265 = (

let uu____9270 = (

let uu____9271 = (

let uu____9277 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (uu____9277)))
in (FStar_SMTEncoding_Util.mkForall uu____9271))
in ((uu____9270), (Some ("not interpretation")), (Some ("l_not-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9265))
in (uu____9264)::[]))))))
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

let uu____9314 = (

let uu____9318 = (

let uu____9320 = (FStar_SMTEncoding_Util.mkApp ((for_all), ((a)::(b)::[])))
in (uu____9320)::[])
in (("Valid"), (uu____9318)))
in (FStar_SMTEncoding_Util.mkApp uu____9314))
in (

let valid_b_x = (

let uu____9324 = (

let uu____9328 = (

let uu____9330 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (uu____9330)::[])
in (("Valid"), (uu____9328)))
in (FStar_SMTEncoding_Util.mkApp uu____9324))
in (

let uu____9332 = (

let uu____9333 = (

let uu____9338 = (

let uu____9339 = (

let uu____9345 = (

let uu____9346 = (

let uu____9349 = (

let uu____9350 = (

let uu____9356 = (

let uu____9359 = (

let uu____9361 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (uu____9361)::[])
in (uu____9359)::[])
in (

let uu____9364 = (

let uu____9365 = (

let uu____9368 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((uu____9368), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9365))
in ((uu____9356), ((xx)::[]), (uu____9364))))
in (FStar_SMTEncoding_Util.mkForall uu____9350))
in ((uu____9349), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9346))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9345)))
in (FStar_SMTEncoding_Util.mkForall uu____9339))
in ((uu____9338), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9333))
in (uu____9332)::[]))))))))))
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

let uu____9416 = (

let uu____9420 = (

let uu____9422 = (FStar_SMTEncoding_Util.mkApp ((for_some), ((a)::(b)::[])))
in (uu____9422)::[])
in (("Valid"), (uu____9420)))
in (FStar_SMTEncoding_Util.mkApp uu____9416))
in (

let valid_b_x = (

let uu____9426 = (

let uu____9430 = (

let uu____9432 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (uu____9432)::[])
in (("Valid"), (uu____9430)))
in (FStar_SMTEncoding_Util.mkApp uu____9426))
in (

let uu____9434 = (

let uu____9435 = (

let uu____9440 = (

let uu____9441 = (

let uu____9447 = (

let uu____9448 = (

let uu____9451 = (

let uu____9452 = (

let uu____9458 = (

let uu____9461 = (

let uu____9463 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (uu____9463)::[])
in (uu____9461)::[])
in (

let uu____9466 = (

let uu____9467 = (

let uu____9470 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((uu____9470), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9467))
in ((uu____9458), ((xx)::[]), (uu____9466))))
in (FStar_SMTEncoding_Util.mkExists uu____9452))
in ((uu____9451), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9448))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9447)))
in (FStar_SMTEncoding_Util.mkForall uu____9441))
in ((uu____9440), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9435))
in (uu____9434)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____9507 = (

let uu____9508 = (

let uu____9513 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (

let uu____9514 = (

let uu____9516 = (varops.mk_unique "typing_range_const")
in Some (uu____9516))
in ((uu____9513), (Some ("Range_const typing")), (uu____9514))))
in FStar_SMTEncoding_Term.Assume (uu____9508))
in (uu____9507)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (

let uu____9779 = (FStar_Util.find_opt (fun uu____9797 -> (match (uu____9797) with
| (l, uu____9807) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)
in (match (uu____9779) with
| None -> begin
[]
end
| Some (uu____9829, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9866 = (encode_function_type_as_formula None None t env)
in (match (uu____9866) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9899 = ((

let uu____9900 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation uu____9900)) || (FStar_Syntax_Util.is_lemma t_norm))
in (match (uu____9899) with
| true -> begin
(

let uu____9904 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____9904) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (

let uu____9916 = (

let uu____9917 = (FStar_Syntax_Subst.compress t_norm)
in uu____9917.FStar_Syntax_Syntax.n)
in (match (uu____9916) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____9922) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____9939 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____9942 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env)))))
end))
end
| uu____9950 -> begin
(

let uu____9951 = (prims.is lid)
in (match (uu____9951) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____9956 = (prims.mk lid vname)
in (match (uu____9956) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end
| uu____9969 -> begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let uu____9971 = (

let uu____9977 = (curried_arrow_formals_comp t_norm)
in (match (uu____9977) with
| (args, comp) -> begin
(match (encode_non_total_function_typ) with
| true -> begin
(

let uu____9992 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (uu____9992)))
end
| uu____9999 -> begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end)
end))
in (match (uu____9971) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____10019 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____10019) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____10032 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___123_10056 -> (match (uu___123_10056) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____10059 = (FStar_Util.prefix vars)
in (match (uu____10059) with
| (uu____10070, (xxsym, uu____10072)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____10082 = (

let uu____10083 = (

let uu____10088 = (

let uu____10089 = (

let uu____10095 = (

let uu____10096 = (

let uu____10099 = (

let uu____10100 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____10100))
in ((vapp), (uu____10099)))
in (FStar_SMTEncoding_Util.mkEq uu____10096))
in ((((vapp)::[])::[]), (vars), (uu____10095)))
in (FStar_SMTEncoding_Util.mkForall uu____10089))
in ((uu____10088), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (uu____10083))
in (uu____10082)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____10112 = (FStar_Util.prefix vars)
in (match (uu____10112) with
| (uu____10123, (xxsym, uu____10125)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____10139 = (

let uu____10140 = (

let uu____10145 = (

let uu____10146 = (

let uu____10152 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____10152)))
in (FStar_SMTEncoding_Util.mkForall uu____10146))
in ((uu____10145), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (uu____10140))
in (uu____10139)::[])))))
end))
end
| uu____10162 -> begin
[]
end)))))
in (

let uu____10163 = (encode_binders None formals env)
in (match (uu____10163) with
| (vars, guards, env', decls1, uu____10179) -> begin
(

let uu____10186 = (match (pre_opt) with
| None -> begin
(

let uu____10191 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____10191), (decls1)))
end
| Some (p) -> begin
(

let uu____10193 = (encode_formula p env')
in (match (uu____10193) with
| (g, ds) -> begin
(

let uu____10200 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____10200), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____10186) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____10209 = (

let uu____10213 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____10213)))
in (FStar_SMTEncoding_Util.mkApp uu____10209))
in (

let uu____10218 = (

let vname_decl = (

let uu____10223 = (

let uu____10229 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____10234 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____10229), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____10223))
in (

let uu____10239 = (

let env = (

let uu___151_10243 = env
in {bindings = uu___151_10243.bindings; depth = uu___151_10243.depth; tcenv = uu___151_10243.tcenv; warn = uu___151_10243.warn; cache = uu___151_10243.cache; nolabels = uu___151_10243.nolabels; use_zfuel_name = uu___151_10243.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (

let uu____10244 = (

let uu____10245 = (head_normal env tt)
in (not (uu____10245)))
in (match (uu____10244) with
| true -> begin
(encode_term_pred None tt env vtok_tm)
end
| uu____10248 -> begin
(encode_term_pred None t_norm env vtok_tm)
end)))
in (match (uu____10239) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let uu____10257 = (match (formals) with
| [] -> begin
(

let uu____10266 = (

let uu____10267 = (

let uu____10269 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_34 -> Some (_0_34)) uu____10269))
in (push_free_var env lid vname uu____10267))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (uu____10266)))
end
| uu____10272 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (

let uu____10277 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) uu____10277))
in (

let name_tok_corr = (

let uu____10279 = (

let uu____10284 = (

let uu____10285 = (

let uu____10291 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____10291)))
in (FStar_SMTEncoding_Util.mkForall uu____10285))
in ((uu____10284), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (uu____10279))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (uu____10257) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (uu____10218) with
| (decls2, env) -> begin
(

let uu____10316 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let uu____10321 = (encode_term res_t env')
in (match (uu____10321) with
| (encoded_res_t, decls) -> begin
(

let uu____10329 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____10329), (decls)))
end)))
in (match (uu____10316) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____10337 = (

let uu____10342 = (

let uu____10343 = (

let uu____10349 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____10349)))
in (FStar_SMTEncoding_Util.mkForall uu____10343))
in ((uu____10342), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (uu____10337))
in (

let freshness = (

let uu____10359 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____10359) with
| true -> begin
(

let uu____10362 = (

let uu____10363 = (

let uu____10369 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (

let uu____10375 = (varops.next_id ())
in ((vname), (uu____10369), (FStar_SMTEncoding_Term.Term_sort), (uu____10375))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____10363))
in (

let uu____10377 = (

let uu____10379 = (pretype_axiom vapp vars)
in (uu____10379)::[])
in (uu____10362)::uu____10377))
end
| uu____10380 -> begin
[]
end))
in (

let g = (

let uu____10383 = (

let uu____10385 = (

let uu____10387 = (

let uu____10389 = (

let uu____10391 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____10391)
in (FStar_List.append freshness uu____10389))
in (FStar_List.append decls3 uu____10387))
in (FStar_List.append decls2 uu____10385))
in (FStar_List.append decls1 uu____10383))
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

let uu____10413 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10413) with
| None -> begin
(

let uu____10436 = (encode_free_var env x t t_norm [])
in (match (uu____10436) with
| (decls, env) -> begin
(

let uu____10451 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10451) with
| (n, x', uu____10470) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, uu____10482) -> begin
((((n), (x))), ([]), (env))
end)))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let uu____10515 = (encode_free_var env lid t tt quals)
in (match (uu____10515) with
| (decls, env) -> begin
(

let uu____10526 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____10526) with
| true -> begin
(

let uu____10530 = (

let uu____10532 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls uu____10532))
in ((uu____10530), (env)))
end
| uu____10535 -> begin
((decls), (env))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____10560 lb -> (match (uu____10560) with
| (decls, env) -> begin
(

let uu____10572 = (

let uu____10576 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env uu____10576 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____10572) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____10600 quals -> (match (uu____10600) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____10649 = (FStar_Util.first_N nbinders formals)
in (match (uu____10649) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun uu____10689 uu____10690 -> (match (((uu____10689), (uu____10690))) with
| ((formal, uu____10700), (binder, uu____10702)) -> begin
(

let uu____10707 = (

let uu____10712 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____10712)))
in FStar_Syntax_Syntax.NT (uu____10707))
end)) formals binders)
in (

let extra_formals = (

let uu____10717 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____10731 -> (match (uu____10731) with
| (x, i) -> begin
(

let uu____10738 = (

let uu___152_10739 = x
in (

let uu____10740 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___152_10739.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___152_10739.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____10740}))
in ((uu____10738), (i)))
end))))
in (FStar_All.pipe_right uu____10717 FStar_Syntax_Util.name_binders))
in (

let body = (

let uu____10752 = (

let uu____10754 = (

let uu____10755 = (FStar_Syntax_Subst.subst subst t)
in uu____10755.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _0_35 -> Some (_0_35)) uu____10754))
in (

let uu____10759 = (

let uu____10760 = (FStar_Syntax_Subst.compress body)
in (

let uu____10761 = (

let uu____10762 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd uu____10762))
in (FStar_Syntax_Syntax.extend_app_n uu____10760 uu____10761)))
in (uu____10759 uu____10752 body.FStar_Syntax_Syntax.pos)))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (

let uu____10821 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____10821) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____10874)::uu____10875 -> begin
(

let uu____10883 = (

let uu____10884 = (FStar_Syntax_Subst.compress t_norm)
in uu____10884.FStar_Syntax_Syntax.n)
in (match (uu____10883) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____10913 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____10913) with
| (formals, c) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (FStar_Syntax_Util.comp_result c)
in (

let uu____10943 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c))
in (match (uu____10943) with
| true -> begin
(

let uu____10963 = (FStar_Util.first_N nformals binders)
in (match (uu____10963) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun uu____11011 uu____11012 -> (match (((uu____11011), (uu____11012))) with
| ((b, uu____11022), (x, uu____11024)) -> begin
(

let uu____11029 = (

let uu____11034 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (uu____11034)))
in FStar_Syntax_Syntax.NT (uu____11029))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))), (false))))
end))
end
| uu____11056 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____11076 = (eta_expand binders formals body tres)
in (match (uu____11076) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end))
end
| uu____11128 -> begin
((((binders), (body), (formals), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____11138) -> begin
(

let uu____11143 = (

let uu____11156 = (aux norm x.FStar_Syntax_Syntax.sort)
in (Prims.fst uu____11156))
in ((uu____11143), (true)))
end
| uu____11195 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| uu____11197 -> begin
(

let uu____11198 = (

let uu____11199 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11200 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____11199 uu____11200)))
in (failwith uu____11198))
end))
end
| uu____11215 -> begin
(

let uu____11216 = (

let uu____11217 = (FStar_Syntax_Subst.compress t_norm)
in uu____11217.FStar_Syntax_Syntax.n)
in (match (uu____11216) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____11246 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____11246) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let uu____11268 = (eta_expand [] formals e tres)
in (match (uu____11268) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end)))
end))
end
| uu____11322 -> begin
(((([]), (e), ([]), (t_norm))), (false))
end))
end)
end)))
in (aux false t_norm)))
in try
(match (()) with
| () -> begin
(

let uu____11350 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp))))
in (match (uu____11350) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____11356 -> begin
(

let uu____11357 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____11398 lb -> (match (uu____11398) with
| (toks, typs, decls, env) -> begin
((

let uu____11449 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____11449) with
| true -> begin
(Prims.raise Let_rec_unencodeable)
end
| uu____11450 -> begin
()
end));
(

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____11452 = (

let uu____11460 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env uu____11460 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____11452) with
| (tok, decl, env) -> begin
(

let uu____11485 = (

let uu____11492 = (

let uu____11498 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((uu____11498), (tok)))
in (uu____11492)::toks)
in ((uu____11485), ((t_norm)::typs), ((decl)::decls), (env)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____11357) with
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
| uu____11600 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| Some (ftok) -> begin
(mk_Apply ftok vars)
end
| None -> begin
(

let uu____11605 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____11605 vars))
end)
end
| uu____11606 -> begin
(

let uu____11607 = (

let uu____11611 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____11611)))
in (FStar_SMTEncoding_Util.mkApp uu____11607))
end)
end))
in (

let uu____11616 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___124_11618 -> (match (uu___124_11618) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____11619 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (

let uu____11622 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation uu____11622))))))
in (match (uu____11616) with
| true -> begin
((decls), (env))
end
| uu____11627 -> begin
(match ((not (is_rec))) with
| true -> begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = uu____11642; FStar_Syntax_Syntax.lbunivs = uu____11643; FStar_Syntax_Syntax.lbtyp = uu____11644; FStar_Syntax_Syntax.lbeff = uu____11645; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____11687 = (destruct_bound_function flid t_norm e)
in (match (uu____11687) with
| ((binders, body, uu____11699, uu____11700), curry) -> begin
(

let uu____11706 = (encode_binders None binders env)
in (match (uu____11706) with
| (vars, guards, env', binder_decls, uu____11722) -> begin
(

let app = (mk_app curry f ftok vars)
in (

let uu____11730 = (

let uu____11735 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____11735) with
| true -> begin
(

let uu____11741 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____11742 = (encode_formula body env')
in ((uu____11741), (uu____11742))))
end
| uu____11747 -> begin
(

let uu____11748 = (encode_term body env')
in ((app), (uu____11748)))
end))
in (match (uu____11730) with
| (app, (body, decls2)) -> begin
(

let eqn = (

let uu____11762 = (

let uu____11767 = (

let uu____11768 = (

let uu____11774 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (uu____11774)))
in (FStar_SMTEncoding_Util.mkForall uu____11768))
in (

let uu____11780 = (

let uu____11782 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (uu____11782))
in ((uu____11767), (uu____11780), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (uu____11762))
in (

let uu____11785 = (

let uu____11787 = (

let uu____11789 = (

let uu____11791 = (

let uu____11793 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) uu____11793))
in (FStar_List.append decls2 uu____11791))
in (FStar_List.append binder_decls uu____11789))
in (FStar_List.append decls uu____11787))
in ((uu____11785), (env))))
end)))
end))
end))))
end
| uu____11796 -> begin
(failwith "Impossible")
end)
end
| uu____11811 -> begin
(

let fuel = (

let uu____11815 = (varops.fresh "fuel")
in ((uu____11815), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env
in (

let uu____11818 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun uu____11857 uu____11858 -> (match (((uu____11857), (uu____11858))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (

let uu____11940 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____11940))
in (

let gtok = (

let uu____11942 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____11942))
in (

let env = (

let uu____11944 = (

let uu____11946 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_36 -> Some (_0_36)) uu____11946))
in (push_free_var env flid gtok uu____11944))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (uu____11818) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 uu____12030 t_norm uu____12032 -> (match (((uu____12030), (uu____12032))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uu____12056; FStar_Syntax_Syntax.lbtyp = uu____12057; FStar_Syntax_Syntax.lbeff = uu____12058; FStar_Syntax_Syntax.lbdef = e}) -> begin
((

let uu____12076 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12076) with
| true -> begin
(

let uu____12077 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____12078 = (FStar_Syntax_Print.term_to_string t_norm)
in (

let uu____12079 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____12077 uu____12078 uu____12079))))
end
| uu____12080 -> begin
()
end));
(

let uu____12081 = (destruct_bound_function flid t_norm e)
in (match (uu____12081) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____12103 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12103) with
| true -> begin
(

let uu____12104 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____12105 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let rec: binders=[%s], body=%s\n" uu____12104 uu____12105)))
end
| uu____12106 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____12108 -> begin
()
end);
(

let uu____12109 = (encode_binders None binders env)
in (match (uu____12109) with
| (vars, guards, env', binder_decls, uu____12127) -> begin
(

let decl_g = (

let uu____12135 = (

let uu____12141 = (

let uu____12143 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____12143)
in ((g), (uu____12141), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____12135))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____12158 = (

let uu____12162 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____12162)))
in (FStar_SMTEncoding_Util.mkApp uu____12158))
in (

let gsapp = (

let uu____12168 = (

let uu____12172 = (

let uu____12174 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____12174)::vars_tm)
in ((g), (uu____12172)))
in (FStar_SMTEncoding_Util.mkApp uu____12168))
in (

let gmax = (

let uu____12178 = (

let uu____12182 = (

let uu____12184 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____12184)::vars_tm)
in ((g), (uu____12182)))
in (FStar_SMTEncoding_Util.mkApp uu____12178))
in (

let uu____12187 = (encode_term body env')
in (match (uu____12187) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____12198 = (

let uu____12203 = (

let uu____12204 = (

let uu____12212 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____12212)))
in (FStar_SMTEncoding_Util.mkForall' uu____12204))
in (

let uu____12223 = (

let uu____12225 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (uu____12225))
in ((uu____12203), (uu____12223), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (uu____12198))
in (

let eqn_f = (

let uu____12229 = (

let uu____12234 = (

let uu____12235 = (

let uu____12241 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____12241)))
in (FStar_SMTEncoding_Util.mkForall uu____12235))
in ((uu____12234), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12229))
in (

let eqn_g' = (

let uu____12250 = (

let uu____12255 = (

let uu____12256 = (

let uu____12262 = (

let uu____12263 = (

let uu____12266 = (

let uu____12267 = (

let uu____12271 = (

let uu____12273 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____12273)::vars_tm)
in ((g), (uu____12271)))
in (FStar_SMTEncoding_Util.mkApp uu____12267))
in ((gsapp), (uu____12266)))
in (FStar_SMTEncoding_Util.mkEq uu____12263))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____12262)))
in (FStar_SMTEncoding_Util.mkForall uu____12256))
in ((uu____12255), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12250))
in (

let uu____12286 = (

let uu____12291 = (encode_binders None formals env0)
in (match (uu____12291) with
| (vars, v_guards, env, binder_decls, uu____12308) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (

let uu____12323 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____12323 ((fuel)::vars)))
in (

let uu____12326 = (

let uu____12331 = (

let uu____12332 = (

let uu____12338 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (uu____12338)))
in (FStar_SMTEncoding_Util.mkForall uu____12332))
in ((uu____12331), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (uu____12326)))
in (

let uu____12350 = (

let uu____12354 = (encode_term_pred None tres env gapp)
in (match (uu____12354) with
| (g_typing, d3) -> begin
(

let uu____12362 = (

let uu____12364 = (

let uu____12365 = (

let uu____12370 = (

let uu____12371 = (

let uu____12377 = (

let uu____12378 = (

let uu____12381 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____12381), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____12378))
in ((((gapp)::[])::[]), ((fuel)::vars), (uu____12377)))
in (FStar_SMTEncoding_Util.mkForall uu____12371))
in ((uu____12370), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12365))
in (uu____12364)::[])
in ((d3), (uu____12362)))
end))
in (match (uu____12350) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____12286) with
| (aux_decls, g_typing) -> begin
(((FStar_List.append binder_decls (FStar_List.append decls2 (FStar_List.append aux_decls ((decl_g)::(decl_g_tok)::[]))))), ((FStar_List.append ((eqn_g)::(eqn_g')::(eqn_f)::[]) g_typing)), (env0))
end)))))
end)))))))))
end));
)
end));
)
end))
in (

let uu____12417 = (

let uu____12424 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun uu____12456 uu____12457 -> (match (((uu____12456), (uu____12457))) with
| ((decls, eqns, env0), (gtok, ty, lb)) -> begin
(

let uu____12533 = (encode_one_binding env0 gtok ty lb)
in (match (uu____12533) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) uu____12424))
in (match (uu____12417) with
| (decls, eqns, env0) -> begin
(

let uu____12573 = (

let uu____12578 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right uu____12578 (FStar_List.partition (fun uu___125_12588 -> (match (uu___125_12588) with
| FStar_SMTEncoding_Term.DeclFun (uu____12589) -> begin
true
end
| uu____12595 -> begin
false
end)))))
in (match (uu____12573) with
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

let uu____12613 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____12613 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> ((

let uu____12646 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12646) with
| true -> begin
(

let uu____12647 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") uu____12647))
end
| uu____12648 -> begin
()
end));
(

let nm = (

let uu____12650 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____12650) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____12653 = (encode_sigelt' env se)
in (match (uu____12653) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(

let uu____12662 = (

let uu____12664 = (

let uu____12665 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12665))
in (uu____12664)::[])
in ((uu____12662), (e)))
end
| uu____12667 -> begin
(

let uu____12668 = (

let uu____12670 = (

let uu____12672 = (

let uu____12673 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12673))
in (uu____12672)::g)
in (

let uu____12674 = (

let uu____12676 = (

let uu____12677 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12677))
in (uu____12676)::[])
in (FStar_List.append uu____12670 uu____12674)))
in ((uu____12668), (e)))
end)
end)));
))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____12685) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, uu____12696) -> begin
(

let uu____12697 = (

let uu____12698 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____12698 Prims.op_Negation))
in (match (uu____12697) with
| true -> begin
(([]), (env))
end
| uu____12703 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____12718 -> begin
(

let uu____12719 = (

let uu____12722 = (

let uu____12723 = (

let uu____12738 = (FStar_All.pipe_left (fun _0_37 -> Some (_0_37)) (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (uu____12738)))
in FStar_Syntax_Syntax.Tm_abs (uu____12723))
in (FStar_Syntax_Syntax.mk uu____12722))
in (uu____12719 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env a -> (

let uu____12791 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (uu____12791) with
| (aname, atok, env) -> begin
(

let uu____12801 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____12801) with
| (formals, uu____12811) -> begin
(

let uu____12818 = (

let uu____12821 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____12821 env))
in (match (uu____12818) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____12829 = (

let uu____12830 = (

let uu____12836 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____12844 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____12836), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____12830))
in (uu____12829)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let uu____12851 = (

let uu____12858 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____12878 -> (match (uu____12878) with
| (bv, uu____12886) -> begin
(

let uu____12887 = (gen_term_var env bv)
in (match (uu____12887) with
| (xxsym, xx, uu____12897) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right uu____12858 FStar_List.split))
in (match (uu____12851) with
| (xs_sorts, xs) -> begin
(

let app = (

let uu____12927 = (

let uu____12931 = (

let uu____12933 = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (uu____12933)::[])
in (("Reify"), (uu____12931)))
in (FStar_SMTEncoding_Util.mkApp uu____12927))
in (

let a_eq = (

let uu____12937 = (

let uu____12942 = (

let uu____12943 = (

let uu____12949 = (

let uu____12950 = (

let uu____12953 = (mk_Apply tm xs_sorts)
in ((app), (uu____12953)))
in (FStar_SMTEncoding_Util.mkEq uu____12950))
in ((((app)::[])::[]), (xs_sorts), (uu____12949)))
in (FStar_SMTEncoding_Util.mkForall uu____12943))
in ((uu____12942), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (uu____12937))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____12966 = (

let uu____12971 = (

let uu____12972 = (

let uu____12978 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____12978)))
in (FStar_SMTEncoding_Util.mkForall uu____12972))
in ((uu____12971), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (uu____12966))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____12989 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____12989) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13005, uu____13006, uu____13007, uu____13008) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let uu____13011 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____13011) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13022, t, quals, uu____13025) -> begin
(

let will_encode_definition = (

let uu____13029 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___126_13031 -> (match (uu___126_13031) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| uu____13034 -> begin
false
end))))
in (not (uu____13029)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____13038 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____13040 = (encode_top_level_val env fv t quals)
in (match (uu____13040) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____13052 = (

let uu____13054 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls uu____13054))
in ((uu____13052), (env)))))
end)))
end))
end
| FStar_Syntax_Syntax.Sig_assume (l, f, uu____13059, uu____13060) -> begin
(

let uu____13063 = (encode_formula f env)
in (match (uu____13063) with
| (f, decls) -> begin
(

let g = (

let uu____13072 = (

let uu____13073 = (

let uu____13078 = (

let uu____13080 = (

let uu____13081 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____13081))
in Some (uu____13080))
in (

let uu____13082 = (

let uu____13084 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (uu____13084))
in ((f), (uu____13078), (uu____13082))))
in FStar_SMTEncoding_Term.Assume (uu____13073))
in (uu____13072)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, uu____13090, quals, uu____13092) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let uu____13100 = (FStar_Util.fold_map (fun env lb -> (

let lid = (

let uu____13107 = (

let uu____13112 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____13112.FStar_Syntax_Syntax.fv_name)
in uu____13107.FStar_Syntax_Syntax.v)
in (

let uu____13116 = (

let uu____13117 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____13117))
in (match (uu____13116) with
| true -> begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let uu____13136 = (encode_sigelt' env val_decl)
in (match (uu____13136) with
| (decls, env) -> begin
((env), (decls))
end)))
end
| uu____13143 -> begin
((env), ([]))
end)))) env (Prims.snd lbs))
in (match (uu____13100) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____13153, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = uu____13155; FStar_Syntax_Syntax.lbtyp = uu____13156; FStar_Syntax_Syntax.lbeff = uu____13157; FStar_Syntax_Syntax.lbdef = uu____13158})::[]), uu____13159, uu____13160, uu____13161, uu____13162) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let uu____13178 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____13178) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid_b2t_x = (

let uu____13196 = (

let uu____13200 = (

let uu____13202 = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (uu____13202)::[])
in (("Valid"), (uu____13200)))
in (FStar_SMTEncoding_Util.mkApp uu____13196))
in (

let decls = (

let uu____13207 = (

let uu____13209 = (

let uu____13210 = (

let uu____13215 = (

let uu____13216 = (

let uu____13222 = (

let uu____13223 = (

let uu____13226 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (uu____13226)))
in (FStar_SMTEncoding_Util.mkEq uu____13223))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (uu____13222)))
in (FStar_SMTEncoding_Util.mkForall uu____13216))
in ((uu____13215), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (uu____13210))
in (uu____13209)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::uu____13207)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____13244, uu____13245, uu____13246, quals, uu____13248) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___127_13256 -> (match (uu___127_13256) with
| FStar_Syntax_Syntax.Discriminator (uu____13257) -> begin
true
end
| uu____13258 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____13260, uu____13261, lids, quals, uu____13264) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____13273 = (

let uu____13274 = (FStar_List.hd l.FStar_Ident.ns)
in uu____13274.FStar_Ident.idText)
in (uu____13273 = "Prims"))))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___128_13276 -> (match (uu___128_13276) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____13277 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____13280, uu____13281, quals, uu____13283) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___129_13295 -> (match (uu___129_13295) with
| FStar_Syntax_Syntax.Projector (uu____13296) -> begin
true
end
| uu____13299 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____13306 = (try_lookup_free_var env l)
in (match (uu____13306) with
| Some (uu____13310) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, (lb)::[]), uu____13319, uu____13320, quals, uu____13322) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let uu____13334 = (

let uu____13335 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in uu____13335.FStar_Syntax_Syntax.n)
in (match (uu____13334) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____13342) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let uu____13399 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____13399) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let uu___155_13416 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___155_13416.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___155_13416.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___155_13416.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___155_13416.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___155_13416.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___155_13416.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___155_13416.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___155_13416.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___155_13416.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___155_13416.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___155_13416.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___155_13416.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___155_13416.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___155_13416.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___155_13416.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___155_13416.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___155_13416.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___155_13416.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___155_13416.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___155_13416.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___155_13416.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___155_13416.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___155_13416.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (

let uu____13417 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals uu____13417)))
end))
in (

let lb = (

let uu___156_13421 = lb
in {FStar_Syntax_Syntax.lbname = uu___156_13421.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___156_13421.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = uu___156_13421.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in ((

let uu____13423 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____13423) with
| true -> begin
(

let uu____13424 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____13425 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____13426 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print3 "%s: Reified %s\nto %s\n" uu____13424 uu____13425 uu____13426))))
end
| uu____13427 -> begin
()
end));
(encode_top_level_let env ((is_rec), ((lb)::[])) quals);
))))))
end
| uu____13429 -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____13433, uu____13434, quals, uu____13436) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____13450, uu____13451, uu____13452) -> begin
(

let uu____13459 = (encode_signature env ses)
in (match (uu____13459) with
| (g, env) -> begin
(

let uu____13469 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___130_13479 -> (match (uu___130_13479) with
| FStar_SMTEncoding_Term.Assume (uu____13480, Some ("inversion axiom"), uu____13481) -> begin
false
end
| uu____13485 -> begin
true
end))))
in (match (uu____13469) with
| (g', inversions) -> begin
(

let uu____13494 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___131_13504 -> (match (uu___131_13504) with
| FStar_SMTEncoding_Term.DeclFun (uu____13505) -> begin
true
end
| uu____13511 -> begin
false
end))))
in (match (uu____13494) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____13522, tps, k, uu____13525, datas, quals, uu____13528) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___132_13537 -> (match (uu___132_13537) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| uu____13538 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____13561 = c
in (match (uu____13561) with
| (name, args, uu____13573, uu____13574, uu____13575) -> begin
(

let uu____13582 = (

let uu____13583 = (

let uu____13589 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (uu____13589), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____13583))
in (uu____13582)::[])
end))
end
| uu____13599 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____13614 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____13617 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____13617 FStar_Option.isNone)))))
in (match (uu____13614) with
| true -> begin
[]
end
| uu____13627 -> begin
(

let uu____13628 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13628) with
| (xxsym, xx) -> begin
(

let uu____13634 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____13645 l -> (match (uu____13645) with
| (out, decls) -> begin
(

let uu____13657 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____13657) with
| (uu____13663, data_t) -> begin
(

let uu____13665 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____13665) with
| (args, res) -> begin
(

let indices = (

let uu____13694 = (

let uu____13695 = (FStar_Syntax_Subst.compress res)
in uu____13695.FStar_Syntax_Syntax.n)
in (match (uu____13694) with
| FStar_Syntax_Syntax.Tm_app (uu____13703, indices) -> begin
indices
end
| uu____13719 -> begin
[]
end))
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env uu____13731 -> (match (uu____13731) with
| (x, uu____13735) -> begin
(

let uu____13736 = (

let uu____13737 = (

let uu____13741 = (mk_term_projector_name l x)
in ((uu____13741), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____13737))
in (push_term_var env x uu____13736))
end)) env))
in (

let uu____13743 = (encode_args indices env)
in (match (uu____13743) with
| (indices, decls') -> begin
((match (((FStar_List.length indices) <> (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____13761 -> begin
()
end);
(

let eqs = (

let uu____13763 = (FStar_List.map2 (fun v a -> (

let uu____13771 = (

let uu____13774 = (FStar_SMTEncoding_Util.mkFreeV v)
in ((uu____13774), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____13771))) vars indices)
in (FStar_All.pipe_right uu____13763 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____13776 = (

let uu____13777 = (

let uu____13780 = (

let uu____13781 = (

let uu____13784 = (mk_data_tester env l xx)
in ((uu____13784), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____13781))
in ((out), (uu____13780)))
in (FStar_SMTEncoding_Util.mkOr uu____13777))
in ((uu____13776), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____13634) with
| (data_ax, decls) -> begin
(

let uu____13792 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____13792) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____13803 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____13803 xx tapp))
end
| uu____13805 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____13806 = (

let uu____13811 = (

let uu____13812 = (

let uu____13818 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____13826 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____13818), (uu____13826))))
in (FStar_SMTEncoding_Util.mkForall uu____13812))
in (

let uu____13834 = (

let uu____13836 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (uu____13836))
in ((uu____13811), (Some ("inversion axiom")), (uu____13834))))
in FStar_SMTEncoding_Term.Assume (uu____13806)))
in (

let pattern_guarded_inversion = (

let uu____13841 = ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1")))
in (match (uu____13841) with
| true -> begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (

let uu____13849 = (

let uu____13850 = (

let uu____13855 = (

let uu____13856 = (

let uu____13862 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____13870 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (uu____13862), (uu____13870))))
in (FStar_SMTEncoding_Util.mkForall uu____13856))
in (

let uu____13878 = (

let uu____13880 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (uu____13880))
in ((uu____13855), (Some ("inversion axiom")), (uu____13878))))
in FStar_SMTEncoding_Term.Assume (uu____13850))
in (uu____13849)::[])))
end
| uu____13883 -> begin
[]
end))
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)))
in (

let uu____13884 = (

let uu____13892 = (

let uu____13893 = (FStar_Syntax_Subst.compress k)
in uu____13893.FStar_Syntax_Syntax.n)
in (match (uu____13892) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____13922 -> begin
((tps), (k))
end))
in (match (uu____13884) with
| (formals, res) -> begin
(

let uu____13937 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____13937) with
| (formals, res) -> begin
(

let uu____13944 = (encode_binders None formals env)
in (match (uu____13944) with
| (vars, guards, env', binder_decls, uu____13959) -> begin
(

let uu____13966 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____13966) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____13979 = (

let uu____13983 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____13983)))
in (FStar_SMTEncoding_Util.mkApp uu____13979))
in (

let uu____13988 = (

let tname_decl = (

let uu____13994 = (

let uu____14003 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____14015 -> (match (uu____14015) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (

let uu____14022 = (varops.next_id ())
in ((tname), (uu____14003), (FStar_SMTEncoding_Term.Term_sort), (uu____14022), (false))))
in (constructor_or_logic_type_decl uu____13994))
in (

let uu____14026 = (match (vars) with
| [] -> begin
(

let uu____14033 = (

let uu____14034 = (

let uu____14036 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_38 -> Some (_0_38)) uu____14036))
in (push_free_var env t tname uu____14034))
in (([]), (uu____14033)))
end
| uu____14040 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (

let uu____14046 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____14046))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____14055 = (

let uu____14060 = (

let uu____14061 = (

let uu____14069 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (uu____14069)))
in (FStar_SMTEncoding_Util.mkForall' uu____14061))
in ((uu____14060), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14055))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (uu____14026) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (uu____13988) with
| (decls, env) -> begin
(

let kindingAx = (

let uu____14093 = (encode_term_pred None res env' tapp)
in (match (uu____14093) with
| (k, decls) -> begin
(

let karr = (match (((FStar_List.length formals) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____14107 = (

let uu____14108 = (

let uu____14113 = (

let uu____14114 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____14114))
in ((uu____14113), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14108))
in (uu____14107)::[])
end
| uu____14117 -> begin
[]
end)
in (

let uu____14118 = (

let uu____14120 = (

let uu____14122 = (

let uu____14123 = (

let uu____14128 = (

let uu____14129 = (

let uu____14135 = (FStar_SMTEncoding_Util.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (uu____14135)))
in (FStar_SMTEncoding_Util.mkForall uu____14129))
in ((uu____14128), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14123))
in (uu____14122)::[])
in (FStar_List.append karr uu____14120))
in (FStar_List.append decls uu____14118)))
end))
in (

let aux = (

let uu____14145 = (

let uu____14147 = (inversion_axioms tapp vars)
in (

let uu____14149 = (

let uu____14151 = (pretype_axiom tapp vars)
in (uu____14151)::[])
in (FStar_List.append uu____14147 uu____14149)))
in (FStar_List.append kindingAx uu____14145))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14156, uu____14157, uu____14158, uu____14159, uu____14160, uu____14161, uu____14162) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14169, t, uu____14171, n_tps, quals, uu____14174, drange) -> begin
(

let uu____14180 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____14180) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____14191 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____14191) with
| (formals, t_res) -> begin
(

let uu____14213 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____14213) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____14222 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____14222) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (

let uu____14255 = (mk_term_projector_name d x)
in ((uu____14255), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (

let uu____14257 = (

let uu____14266 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (uu____14266), (true)))
in (FStar_All.pipe_right uu____14257 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____14286 = (encode_term_pred None t env ddtok_tm)
in (match (uu____14286) with
| (tok_typing, decls3) -> begin
(

let uu____14293 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____14293) with
| (vars', guards', env'', decls_formals, uu____14308) -> begin
(

let uu____14315 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (uu____14315) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____14334 -> begin
(

let uu____14338 = (

let uu____14339 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____14339))
in (uu____14338)::[])
end)
in (

let encode_elim = (fun uu____14346 -> (

let uu____14347 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____14347) with
| (head, args) -> begin
(

let uu____14376 = (

let uu____14377 = (FStar_Syntax_Subst.compress head)
in uu____14377.FStar_Syntax_Syntax.n)
in (match (uu____14376) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____14395 = (encode_args args env')
in (match (uu____14395) with
| (encoded_args, arg_decls) -> begin
(

let uu____14406 = (FStar_List.fold_left (fun uu____14417 arg -> (match (uu____14417) with
| (env, arg_vars, eqns) -> begin
(

let uu____14436 = (

let uu____14440 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env uu____14440))
in (match (uu____14436) with
| (uu____14446, xv, env) -> begin
(

let uu____14449 = (

let uu____14451 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____14451)::eqns)
in ((env), ((xv)::arg_vars), (uu____14449)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (uu____14406) with
| (uu____14459, arg_vars, eqns) -> begin
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

let uu____14480 = (

let uu____14485 = (

let uu____14486 = (

let uu____14492 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14498 = (

let uu____14499 = (

let uu____14502 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (uu____14502)))
in (FStar_SMTEncoding_Util.mkImp uu____14499))
in ((((ty_pred)::[])::[]), (uu____14492), (uu____14498))))
in (FStar_SMTEncoding_Util.mkForall uu____14486))
in ((uu____14485), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (uu____14480))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____14516 = (varops.fresh "x")
in ((uu____14516), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____14518 = (

let uu____14523 = (

let uu____14524 = (

let uu____14530 = (

let uu____14533 = (

let uu____14535 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in (uu____14535)::[])
in (uu____14533)::[])
in (

let uu____14538 = (

let uu____14539 = (

let uu____14542 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____14543 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in ((uu____14542), (uu____14543))))
in (FStar_SMTEncoding_Util.mkImp uu____14539))
in ((uu____14530), ((x)::[]), (uu____14538))))
in (FStar_SMTEncoding_Util.mkForall uu____14524))
in (

let uu____14553 = (

let uu____14555 = (varops.mk_unique "lextop")
in Some (uu____14555))
in ((uu____14523), (Some ("lextop is top")), (uu____14553))))
in FStar_SMTEncoding_Term.Assume (uu____14518))))
end
| uu____14558 -> begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(

let uu____14569 = (

let uu____14570 = (FStar_SMTEncoding_Util.mkFreeV v)
in (FStar_SMTEncoding_Util.mk_Precedes uu____14570 dapp))
in (uu____14569)::[])
end
| uu____14571 -> begin
(failwith "unexpected sort")
end))))
in (

let uu____14573 = (

let uu____14578 = (

let uu____14579 = (

let uu____14585 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14591 = (

let uu____14592 = (

let uu____14595 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____14595)))
in (FStar_SMTEncoding_Util.mkImp uu____14592))
in ((((ty_pred)::[])::[]), (uu____14585), (uu____14591))))
in (FStar_SMTEncoding_Util.mkForall uu____14579))
in ((uu____14578), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (uu____14573)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| uu____14606 -> begin
((

let uu____14608 = (

let uu____14609 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____14610 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____14609 uu____14610)))
in (FStar_Errors.warn drange uu____14608));
(([]), ([]));
)
end))
end)))
in (

let uu____14613 = (encode_elim ())
in (match (uu____14613) with
| (decls2, elim) -> begin
(

let g = (

let uu____14625 = (

let uu____14627 = (

let uu____14629 = (

let uu____14631 = (

let uu____14633 = (

let uu____14634 = (

let uu____14640 = (

let uu____14642 = (

let uu____14643 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____14643))
in Some (uu____14642))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____14640)))
in FStar_SMTEncoding_Term.DeclFun (uu____14634))
in (uu____14633)::[])
in (

let uu____14646 = (

let uu____14648 = (

let uu____14650 = (

let uu____14652 = (

let uu____14654 = (

let uu____14656 = (

let uu____14658 = (

let uu____14659 = (

let uu____14664 = (

let uu____14665 = (

let uu____14671 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____14671)))
in (FStar_SMTEncoding_Util.mkForall uu____14665))
in ((uu____14664), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (uu____14659))
in (

let uu____14679 = (

let uu____14681 = (

let uu____14682 = (

let uu____14687 = (

let uu____14688 = (

let uu____14694 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____14700 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____14694), (uu____14700))))
in (FStar_SMTEncoding_Util.mkForall uu____14688))
in ((uu____14687), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (uu____14682))
in (uu____14681)::[])
in (uu____14658)::uu____14679))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::uu____14656)
in (FStar_List.append uu____14654 elim))
in (FStar_List.append decls_pred uu____14652))
in (FStar_List.append decls_formals uu____14650))
in (FStar_List.append proxy_fresh uu____14648))
in (FStar_List.append uu____14631 uu____14646)))
in (FStar_List.append decls3 uu____14629))
in (FStar_List.append decls2 uu____14627))
in (FStar_List.append binder_decls uu____14625))
in (((FStar_List.append datacons g)), (env)))
end)))))
end))
end))
end))))))))
end)))
end))
end)))
end))
end))
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____14723 se -> (match (uu____14723) with
| (g, env) -> begin
(

let uu____14735 = (encode_sigelt env se)
in (match (uu____14735) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____14771 -> (match (uu____14771) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____14789) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____14794 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____14794) with
| true -> begin
(

let uu____14795 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14796 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14797 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____14795 uu____14796 uu____14797))))
end
| uu____14798 -> begin
()
end));
(

let uu____14799 = (encode_term t1 env)
in (match (uu____14799) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____14809 = (

let uu____14813 = (

let uu____14814 = (

let uu____14815 = (FStar_Util.digest_of_string t_hash)
in (

let uu____14816 = (

let uu____14817 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____14817))
in (Prims.strcat uu____14815 uu____14816)))
in (Prims.strcat "x_" uu____14814))
in (new_term_constant_from_string env x uu____14813))
in (match (uu____14809) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = (

let uu____14828 = (FStar_Options.log_queries ())
in (match (uu____14828) with
| true -> begin
(

let uu____14830 = (

let uu____14831 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14832 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14833 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____14831 uu____14832 uu____14833))))
in Some (uu____14830))
end
| uu____14834 -> begin
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
| FStar_TypeChecker_Env.Binding_lid (x, (uu____14846, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____14855 = (encode_free_var env fv t t_norm [])
in (match (uu____14855) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let uu____14874 = (encode_sigelt env se)
in (match (uu____14874) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____14884 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____14884) with
| (uu____14896, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun uu____14941 -> (match (uu____14941) with
| (l, uu____14948, uu____14949) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____14970 -> (match (uu____14970) with
| (l, uu____14978, uu____14979) -> begin
(

let uu____14984 = (FStar_All.pipe_left (fun _0_39 -> FStar_SMTEncoding_Term.Echo (_0_39)) (Prims.fst l))
in (

let uu____14985 = (

let uu____14987 = (

let uu____14988 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____14988))
in (uu____14987)::[])
in (uu____14984)::uu____14985))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____14999 = (

let uu____15001 = (

let uu____15002 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____15002; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (uu____15001)::[])
in (FStar_ST.write last_env uu____14999)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (

let uu____15020 = (FStar_ST.read last_env)
in (match (uu____15020) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____15026 -> begin
(

let uu___157_15028 = e
in {bindings = uu___157_15028.bindings; depth = uu___157_15028.depth; tcenv = tcenv; warn = uu___157_15028.warn; cache = uu___157_15028.cache; nolabels = uu___157_15028.nolabels; use_zfuel_name = uu___157_15028.use_zfuel_name; encode_non_total_function_typ = uu___157_15028.encode_non_total_function_typ})
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____15032 = (FStar_ST.read last_env)
in (match (uu____15032) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____15037)::tl -> begin
(FStar_ST.write last_env ((env)::tl))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____15045 -> (

let uu____15046 = (FStar_ST.read last_env)
in (match (uu____15046) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd)::tl -> begin
(

let refs = (FStar_Util.smap_copy hd.cache)
in (

let top = (

let uu___158_15067 = hd
in {bindings = uu___158_15067.bindings; depth = uu___158_15067.depth; tcenv = uu___158_15067.tcenv; warn = uu___158_15067.warn; cache = refs; nolabels = uu___158_15067.nolabels; use_zfuel_name = uu___158_15067.use_zfuel_name; encode_non_total_function_typ = uu___158_15067.encode_non_total_function_typ})
in (FStar_ST.write last_env ((top)::(hd)::tl))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____15073 -> (

let uu____15074 = (FStar_ST.read last_env)
in (match (uu____15074) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____15079)::tl -> begin
(FStar_ST.write last_env tl)
end)))


let mark_env : Prims.unit  ->  Prims.unit = (fun uu____15087 -> (push_env ()))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15090 -> (pop_env ()))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15093 -> (

let uu____15094 = (FStar_ST.read last_env)
in (match (uu____15094) with
| (hd)::(uu____15100)::tl -> begin
(FStar_ST.write last_env ((hd)::tl))
end
| uu____15106 -> begin
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

let uu____15151 = (FStar_Options.log_queries ())
in (match (uu____15151) with
| true -> begin
(

let uu____15153 = (

let uu____15154 = (

let uu____15155 = (

let uu____15156 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____15156 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____15155))
in FStar_SMTEncoding_Term.Caption (uu____15154))
in (uu____15153)::decls)
end
| uu____15161 -> begin
decls
end)))
in (

let env = (get_env tcenv)
in (

let uu____15163 = (encode_sigelt env se)
in (match (uu____15163) with
| (decls, env) -> begin
((set_env env);
(

let uu____15169 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____15169));
)
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____15178 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____15180 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15180) with
| true -> begin
(

let uu____15181 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____15181))
end
| uu____15184 -> begin
()
end));
(

let env = (get_env tcenv)
in (

let uu____15186 = (encode_signature (

let uu___159_15190 = env
in {bindings = uu___159_15190.bindings; depth = uu___159_15190.depth; tcenv = uu___159_15190.tcenv; warn = false; cache = uu___159_15190.cache; nolabels = uu___159_15190.nolabels; use_zfuel_name = uu___159_15190.use_zfuel_name; encode_non_total_function_typ = uu___159_15190.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____15186) with
| (decls, env) -> begin
(

let caption = (fun decls -> (

let uu____15202 = (FStar_Options.log_queries ())
in (match (uu____15202) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____15205 -> begin
decls
end)))
in ((set_env (

let uu___160_15207 = env
in {bindings = uu___160_15207.bindings; depth = uu___160_15207.depth; tcenv = uu___160_15207.tcenv; warn = true; cache = uu___160_15207.cache; nolabels = uu___160_15207.nolabels; use_zfuel_name = uu___160_15207.use_zfuel_name; encode_non_total_function_typ = uu___160_15207.encode_non_total_function_typ}));
(

let uu____15209 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15209) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____15210 -> begin
()
end));
(

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls));
))
end)));
)))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____15244 = (

let uu____15245 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____15245.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____15244));
(

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____15253 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____15274 = (aux rest)
in (match (uu____15274) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let uu____15290 = (

let uu____15292 = (FStar_Syntax_Syntax.mk_binder (

let uu___161_15293 = x
in {FStar_Syntax_Syntax.ppname = uu___161_15293.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___161_15293.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (uu____15292)::out)
in ((uu____15290), (rest))))
end))
end
| uu____15296 -> begin
(([]), (bindings))
end))
in (

let uu____15300 = (aux bindings)
in (match (uu____15300) with
| (closing, bindings) -> begin
(

let uu____15314 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((uu____15314), (bindings)))
end)))
in (match (uu____15253) with
| (q, bindings) -> begin
(

let uu____15327 = (

let uu____15330 = (FStar_List.filter (fun uu___133_15332 -> (match (uu___133_15332) with
| FStar_TypeChecker_Env.Binding_sig (uu____15333) -> begin
false
end
| uu____15337 -> begin
true
end)) bindings)
in (encode_env_bindings env uu____15330))
in (match (uu____15327) with
| (env_decls, env) -> begin
((

let uu____15348 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____15348) with
| true -> begin
(

let uu____15349 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____15349))
end
| uu____15350 -> begin
()
end));
(

let uu____15351 = (encode_formula q env)
in (match (uu____15351) with
| (phi, qdecls) -> begin
(

let uu____15363 = (

let uu____15366 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____15366 phi))
in (match (uu____15363) with
| (labels, phi) -> begin
(

let uu____15376 = (encode_labels labels)
in (match (uu____15376) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____15397 = (

let uu____15402 = (FStar_SMTEncoding_Util.mkNot phi)
in (

let uu____15403 = (

let uu____15405 = (varops.mk_unique "@query")
in Some (uu____15405))
in ((uu____15402), (Some ("query")), (uu____15403))))
in FStar_SMTEncoding_Term.Assume (uu____15397))
in (

let suffix = (

let uu____15410 = (

let uu____15412 = (

let uu____15414 = (FStar_Options.print_z3_statistics ())
in (match (uu____15414) with
| true -> begin
(FStar_SMTEncoding_Term.PrintStats)::[]
end
| uu____15416 -> begin
[]
end))
in (FStar_List.append uu____15412 ((FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in (FStar_List.append label_suffix uu____15410))
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

let uu____15427 = (encode_formula q env)
in (match (uu____15427) with
| (f, uu____15431) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____15433) -> begin
true
end
| uu____15436 -> begin
false
end);
)
end));
)))






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

let uu____4356 = (

let uu____4360 = (

let uu____4361 = ((FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown) None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_bv uu____4361))
in (gen_term_var env uu____4360))
in (match (uu____4356) with
| (scrsym, scr', env) -> begin
(

let uu____4375 = (encode_term e env)
in (match (uu____4375) with
| (scr, decls) -> begin
(

let uu____4382 = (

let encode_branch = (fun b uu____4398 -> (match (uu____4398) with
| (else_case, decls) -> begin
(

let uu____4409 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____4409) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun uu____4439 uu____4440 -> (match (((uu____4439), (uu____4440))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr')
in (

let projections = (pattern.projections scr')
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env uu____4477 -> (match (uu____4477) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let uu____4482 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let uu____4497 = (encode_term w env)
in (match (uu____4497) with
| (w, decls2) -> begin
(

let uu____4505 = (

let uu____4506 = (

let uu____4509 = (

let uu____4510 = (

let uu____4513 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w), (uu____4513)))
in (FStar_SMTEncoding_Util.mkEq uu____4510))
in ((guard), (uu____4509)))
in (FStar_SMTEncoding_Util.mkAnd uu____4506))
in ((uu____4505), (decls2)))
end))
end)
in (match (uu____4482) with
| (guard, decls2) -> begin
(

let uu____4521 = (encode_br br env)
in (match (uu____4521) with
| (br, decls3) -> begin
(

let uu____4529 = (FStar_SMTEncoding_Util.mkITE ((guard), (br), (else_case)))
in ((uu____4529), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end))
in (FStar_List.fold_right encode_branch pats ((default_case), (decls))))
in (match (uu____4382) with
| (match_tm, decls) -> begin
(

let uu____4541 = (FStar_SMTEncoding_Term.mkLet' (((((((scrsym), (FStar_SMTEncoding_Term.Term_sort))), (scr)))::[]), (match_tm)) FStar_Range.dummyRange)
in ((uu____4541), (decls)))
end))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| uu____4572 -> begin
(

let uu____4573 = (encode_one_pat env pat)
in (uu____4573)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____4585 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4585) with
| true -> begin
(

let uu____4586 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____4586))
end
| uu____4587 -> begin
()
end));
(

let uu____4588 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____4588) with
| (vars, pat_term) -> begin
(

let uu____4598 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____4621 v -> (match (uu____4621) with
| (env, vars) -> begin
(

let uu____4649 = (gen_term_var env v)
in (match (uu____4649) with
| (xx, uu____4661, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (uu____4598) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4708) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____4716 = (

let uu____4719 = (encode_const c)
in ((scrutinee), (uu____4719)))
in (FStar_SMTEncoding_Util.mkEq uu____4716))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (

let tc_name = (FStar_TypeChecker_Env.typ_of_datacon env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____4738 = (FStar_TypeChecker_Env.datacons_of_typ env.tcenv tc_name)
in (match (uu____4738) with
| (uu____4742, (uu____4743)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____4745 -> begin
(mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
end)))
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4766 -> (match (uu____4766) with
| (arg, uu____4772) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____4782 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____4782)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4801) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____4816) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____4831 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4853 -> (match (uu____4853) with
| (arg, uu____4862) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____4872 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____4872)))
end))))
in (FStar_All.pipe_right uu____4831 FStar_List.flatten))
end))
in (

let pat_term = (fun uu____4888 -> (encode_term pat_term env))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____4895 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____4910 uu____4911 -> (match (((uu____4910), (uu____4911))) with
| ((tms, decls), (t, uu____4931)) -> begin
(

let uu____4942 = (encode_term t env)
in (match (uu____4942) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____4895) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let list_elements = (fun e -> (

let uu____4980 = (FStar_Syntax_Util.list_elements e)
in (match (uu____4980) with
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

let uu____4998 = (

let uu____5008 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____5008 FStar_Syntax_Util.head_and_args))
in (match (uu____4998) with
| (head, args) -> begin
(

let uu____5039 = (

let uu____5047 = (

let uu____5048 = (FStar_Syntax_Util.un_uinst head)
in uu____5048.FStar_Syntax_Syntax.n)
in ((uu____5047), (args)))
in (match (uu____5039) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____5062, uu____5063))::((e, uu____5065))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5096))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| uu____5117 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let uu____5150 = (

let uu____5160 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right uu____5160 FStar_Syntax_Util.head_and_args))
in (match (uu____5150) with
| (head, args) -> begin
(

let uu____5189 = (

let uu____5197 = (

let uu____5198 = (FStar_Syntax_Util.un_uinst head)
in uu____5198.FStar_Syntax_Syntax.n)
in ((uu____5197), (args)))
in (match (uu____5189) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5211))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| uu____5231 -> begin
None
end))
end)))
in (match (elts) with
| (t)::[] -> begin
(

let uu____5249 = (smt_pat_or t)
in (match (uu____5249) with
| Some (e) -> begin
(

let uu____5265 = (list_elements e)
in (FStar_All.pipe_right uu____5265 (FStar_List.map (fun branch -> (

let uu____5282 = (list_elements branch)
in (FStar_All.pipe_right uu____5282 (FStar_List.map one_pat)))))))
end
| uu____5296 -> begin
(

let uu____5300 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5300)::[])
end))
end
| uu____5331 -> begin
(

let uu____5333 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5333)::[])
end))))
in (

let uu____5364 = (

let uu____5380 = (

let uu____5381 = (FStar_Syntax_Subst.compress t)
in uu____5381.FStar_Syntax_Syntax.n)
in (match (uu____5380) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____5411 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____5411) with
| (binders, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____5446; FStar_Syntax_Syntax.effect_name = uu____5447; FStar_Syntax_Syntax.result_typ = uu____5448; FStar_Syntax_Syntax.effect_args = ((pre, uu____5450))::((post, uu____5452))::((pats, uu____5454))::[]; FStar_Syntax_Syntax.flags = uu____5455}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (

let uu____5489 = (lemma_pats pats')
in ((binders), (pre), (post), (uu____5489))))
end
| uu____5508 -> begin
(failwith "impos")
end)
end))
end
| uu____5524 -> begin
(failwith "Impos")
end))
in (match (uu____5364) with
| (binders, pre, post, patterns) -> begin
(

let uu____5568 = (encode_binders None binders env)
in (match (uu____5568) with
| (vars, guards, env, decls, uu____5583) -> begin
(

let uu____5590 = (

let uu____5597 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let uu____5628 = (

let uu____5633 = (FStar_All.pipe_right branch (FStar_List.map (fun uu____5649 -> (match (uu____5649) with
| (t, uu____5656) -> begin
(encode_term t (

let uu___144_5659 = env
in {bindings = uu___144_5659.bindings; depth = uu___144_5659.depth; tcenv = uu___144_5659.tcenv; warn = uu___144_5659.warn; cache = uu___144_5659.cache; nolabels = uu___144_5659.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___144_5659.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right uu____5633 FStar_List.unzip))
in (match (uu____5628) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right uu____5597 FStar_List.unzip))
in (match (uu____5590) with
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

let uu____5723 = (

let uu____5724 = (FStar_SMTEncoding_Util.mkFreeV l)
in (FStar_SMTEncoding_Util.mk_Precedes uu____5724 e))
in (uu____5723)::p))))
end
| uu____5725 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (

let uu____5754 = (FStar_SMTEncoding_Util.mk_Precedes tl e)
in (uu____5754)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(

let uu____5762 = (

let uu____5763 = (FStar_SMTEncoding_Util.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mk_LexCons uu____5763 tl))
in (aux uu____5762 vars))
end
| uu____5764 -> begin
pats
end))
in (

let uu____5768 = (FStar_SMTEncoding_Util.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux uu____5768 vars)))
end)
end)
in (

let env = (

let uu___145_5770 = env
in {bindings = uu___145_5770.bindings; depth = uu___145_5770.depth; tcenv = uu___145_5770.tcenv; warn = uu___145_5770.warn; cache = uu___145_5770.cache; nolabels = true; use_zfuel_name = uu___145_5770.use_zfuel_name; encode_non_total_function_typ = uu___145_5770.encode_non_total_function_typ})
in (

let uu____5771 = (

let uu____5774 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____5774 env))
in (match (uu____5771) with
| (pre, decls'') -> begin
(

let uu____5779 = (

let uu____5782 = (FStar_Syntax_Util.unmeta post)
in (encode_formula uu____5782 env))
in (match (uu____5779) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (

let uu____5789 = (

let uu____5790 = (

let uu____5796 = (

let uu____5797 = (

let uu____5800 = (FStar_SMTEncoding_Util.mk_and_l ((pre)::guards))
in ((uu____5800), (post)))
in (FStar_SMTEncoding_Util.mkImp uu____5797))
in ((pats), (vars), (uu____5796)))
in (FStar_SMTEncoding_Util.mkForall uu____5790))
in ((uu____5789), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> (

let uu____5813 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____5813) with
| true -> begin
(

let uu____5814 = (FStar_Syntax_Print.tag_of_term phi)
in (

let uu____5815 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____5814 uu____5815)))
end
| uu____5816 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____5842 = (FStar_Util.fold_map (fun decls x -> (

let uu____5855 = (encode_term (Prims.fst x) env)
in (match (uu____5855) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____5842) with
| (decls, args) -> begin
(

let uu____5872 = (

let uu___146_5873 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___146_5873.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___146_5873.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____5872), (decls)))
end)))
in (

let const_op = (fun f r uu____5892 -> (

let uu____5895 = (f r)
in ((uu____5895), ([]))))
in (

let un_op = (fun f l -> (

let uu____5911 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____5911)))
in (

let bin_op = (fun f uu___119_5924 -> (match (uu___119_5924) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____5932 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____5959 = (FStar_Util.fold_map (fun decls uu____5968 -> (match (uu____5968) with
| (t, uu____5976) -> begin
(

let uu____5977 = (encode_formula t env)
in (match (uu____5977) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (uu____5959) with
| (decls, phis) -> begin
(

let uu____5994 = (

let uu___147_5995 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___147_5995.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___147_5995.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____5994), (decls)))
end)))
in (

let eq_op = (fun r uu___120_6011 -> (match (uu___120_6011) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(

let uu____6071 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____6071 r ((e1)::(e2)::[])))
end
| l -> begin
(

let uu____6091 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____6091 r l))
end))
in (

let mk_imp = (fun r uu___121_6110 -> (match (uu___121_6110) with
| ((lhs, uu____6114))::((rhs, uu____6116))::[] -> begin
(

let uu____6137 = (encode_formula rhs env)
in (match (uu____6137) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____6146) -> begin
((l1), (decls1))
end
| uu____6149 -> begin
(

let uu____6150 = (encode_formula lhs env)
in (match (uu____6150) with
| (l2, decls2) -> begin
(

let uu____6157 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____6157), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____6159 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___122_6174 -> (match (uu___122_6174) with
| ((guard, uu____6178))::((_then, uu____6180))::((_else, uu____6182))::[] -> begin
(

let uu____6211 = (encode_formula guard env)
in (match (uu____6211) with
| (g, decls1) -> begin
(

let uu____6218 = (encode_formula _then env)
in (match (uu____6218) with
| (t, decls2) -> begin
(

let uu____6225 = (encode_formula _else env)
in (match (uu____6225) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____6234 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____6253 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____6253)))
in (

let connectives = (

let uu____6265 = (

let uu____6274 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Syntax_Const.and_lid), (uu____6274)))
in (

let uu____6287 = (

let uu____6297 = (

let uu____6306 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Syntax_Const.or_lid), (uu____6306)))
in (

let uu____6319 = (

let uu____6329 = (

let uu____6339 = (

let uu____6348 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Syntax_Const.iff_lid), (uu____6348)))
in (

let uu____6361 = (

let uu____6371 = (

let uu____6381 = (

let uu____6390 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Syntax_Const.not_lid), (uu____6390)))
in (uu____6381)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::uu____6371)
in (uu____6339)::uu____6361))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::uu____6329)
in (uu____6297)::uu____6319))
in (uu____6265)::uu____6287))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____6552 = (encode_formula phi' env)
in (match (uu____6552) with
| (phi, decls) -> begin
(

let uu____6559 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))) r)
in ((uu____6559), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____6560) -> begin
(

let uu____6565 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula uu____6565 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____6594 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____6594) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____6602; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____6604; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____6620 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____6620) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____6652)::((x, uu____6654))::((t, uu____6656))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let uu____6690 = (encode_term x env)
in (match (uu____6690) with
| (x, decls) -> begin
(

let uu____6697 = (encode_term t env)
in (match (uu____6697) with
| (t, decls') -> begin
(

let uu____6704 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((uu____6704), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____6708))::((msg, uu____6710))::((phi, uu____6712))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(

let uu____6746 = (

let uu____6749 = (

let uu____6750 = (FStar_Syntax_Subst.compress r)
in uu____6750.FStar_Syntax_Syntax.n)
in (

let uu____6753 = (

let uu____6754 = (FStar_Syntax_Subst.compress msg)
in uu____6754.FStar_Syntax_Syntax.n)
in ((uu____6749), (uu____6753))))
in (match (uu____6746) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____6761))) -> begin
(

let phi = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false)))))))) None r)
in (fallback phi))
end
| uu____6777 -> begin
(fallback phi)
end))
end
| uu____6780 when (head_redex env head) -> begin
(

let uu____6788 = (whnf env phi)
in (encode_formula uu____6788 env))
end
| uu____6789 -> begin
(

let uu____6797 = (encode_term phi env)
in (match (uu____6797) with
| (tt, decls) -> begin
(

let uu____6804 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___148_6805 = tt
in {FStar_SMTEncoding_Term.tm = uu___148_6805.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___148_6805.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((uu____6804), (decls)))
end))
end))
end
| uu____6808 -> begin
(

let uu____6809 = (encode_term phi env)
in (match (uu____6809) with
| (tt, decls) -> begin
(

let uu____6816 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___149_6817 = tt
in {FStar_SMTEncoding_Term.tm = uu___149_6817.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___149_6817.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((uu____6816), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let uu____6844 = (encode_binders None bs env)
in (match (uu____6844) with
| (vars, guards, env, decls, uu____6866) -> begin
(

let uu____6873 = (

let uu____6880 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____6903 = (

let uu____6908 = (FStar_All.pipe_right p (FStar_List.map (fun uu____6922 -> (match (uu____6922) with
| (t, uu____6928) -> begin
(encode_term t (

let uu___150_6929 = env
in {bindings = uu___150_6929.bindings; depth = uu___150_6929.depth; tcenv = uu___150_6929.tcenv; warn = uu___150_6929.warn; cache = uu___150_6929.cache; nolabels = uu___150_6929.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___150_6929.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right uu____6908 FStar_List.unzip))
in (match (uu____6903) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right uu____6880 FStar_List.unzip))
in (match (uu____6873) with
| (pats, decls') -> begin
(

let uu____6981 = (encode_formula body env)
in (match (uu____6981) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____7000; FStar_SMTEncoding_Term.rng = uu____7001})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| uu____7009 -> begin
guards
end)
in (

let uu____7012 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((vars), (pats), (uu____7012), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug phi);
(

let phi = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun uu____7046 -> (match (uu____7046) with
| (x, uu____7050) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats) with
| [] -> begin
()
end
| (hd)::tl -> begin
(

let pat_vars = (

let uu____7056 = (FStar_Syntax_Free.names hd)
in (FStar_List.fold_left (fun out x -> (

let uu____7062 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____7062))) uu____7056 tl))
in (

let uu____7064 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____7076 -> (match (uu____7076) with
| (b, uu____7080) -> begin
(

let uu____7081 = (FStar_Util.set_mem b pat_vars)
in (not (uu____7081)))
end))))
in (match (uu____7064) with
| None -> begin
()
end
| Some (x, uu____7085) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd.FStar_Syntax_Syntax.pos tl)
in (

let uu____7095 = (

let uu____7096 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____7096))
in (FStar_Errors.warn pos uu____7095)))
end)))
end)))
in (

let uu____7097 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____7097) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____7103 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____7139 -> (match (uu____7139) with
| (l, uu____7149) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____7103) with
| None -> begin
(fallback phi)
end
| Some (uu____7172, f) -> begin
(f phi.FStar_Syntax_Syntax.pos arms)
end))
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7201 = (encode_q_body env vars pats body)
in (match (uu____7201) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (

let uu____7227 = (

let uu____7233 = (FStar_SMTEncoding_Util.mkImp ((guard), (body)))
in ((pats), (vars), (uu____7233)))
in (FStar_SMTEncoding_Term.mkForall uu____7227 phi.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7245 = (encode_q_body env vars pats body)
in (match (uu____7245) with
| (vars, pats, guard, body, decls) -> begin
(

let uu____7270 = (

let uu____7271 = (

let uu____7277 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body)))
in ((pats), (vars), (uu____7277)))
in (FStar_SMTEncoding_Term.mkExists uu____7271 phi.FStar_Syntax_Syntax.pos))
in ((uu____7270), (decls)))
end));
)
end))));
)))))))))))))))

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let prims : prims_t = (

let uu____7326 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7326) with
| (asym, a) -> begin
(

let uu____7331 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7331) with
| (xsym, x) -> begin
(

let uu____7336 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7336) with
| (ysym, y) -> begin
(

let quant = (fun vars body x -> (

let xname_decl = (

let uu____7366 = (

let uu____7372 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (uu____7372), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____7366))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (

let uu____7387 = (

let uu____7391 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x), (uu____7391)))
in (FStar_SMTEncoding_Util.mkApp uu____7387))
in (

let xtok = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (

let uu____7399 = (

let uu____7401 = (

let uu____7403 = (

let uu____7405 = (

let uu____7406 = (

let uu____7411 = (

let uu____7412 = (

let uu____7418 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____7418)))
in (FStar_SMTEncoding_Util.mkForall uu____7412))
in ((uu____7411), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (uu____7406))
in (

let uu____7428 = (

let uu____7430 = (

let uu____7431 = (

let uu____7436 = (

let uu____7437 = (

let uu____7443 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____7443)))
in (FStar_SMTEncoding_Util.mkForall uu____7437))
in ((uu____7436), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x)))))
in FStar_SMTEncoding_Term.Assume (uu____7431))
in (uu____7430)::[])
in (uu____7405)::uu____7428))
in (xtok_decl)::uu____7403)
in (xname_decl)::uu____7401)
in ((xtok), (uu____7399))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (

let uu____7493 = (

let uu____7501 = (

let uu____7507 = (

let uu____7508 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7508))
in (quant axy uu____7507))
in ((FStar_Syntax_Const.op_Eq), (uu____7501)))
in (

let uu____7514 = (

let uu____7523 = (

let uu____7531 = (

let uu____7537 = (

let uu____7538 = (

let uu____7539 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____7539))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7538))
in (quant axy uu____7537))
in ((FStar_Syntax_Const.op_notEq), (uu____7531)))
in (

let uu____7545 = (

let uu____7554 = (

let uu____7562 = (

let uu____7568 = (

let uu____7569 = (

let uu____7570 = (

let uu____7573 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7574 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7573), (uu____7574))))
in (FStar_SMTEncoding_Util.mkLT uu____7570))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7569))
in (quant xy uu____7568))
in ((FStar_Syntax_Const.op_LT), (uu____7562)))
in (

let uu____7580 = (

let uu____7589 = (

let uu____7597 = (

let uu____7603 = (

let uu____7604 = (

let uu____7605 = (

let uu____7608 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7609 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7608), (uu____7609))))
in (FStar_SMTEncoding_Util.mkLTE uu____7605))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7604))
in (quant xy uu____7603))
in ((FStar_Syntax_Const.op_LTE), (uu____7597)))
in (

let uu____7615 = (

let uu____7624 = (

let uu____7632 = (

let uu____7638 = (

let uu____7639 = (

let uu____7640 = (

let uu____7643 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7644 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7643), (uu____7644))))
in (FStar_SMTEncoding_Util.mkGT uu____7640))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7639))
in (quant xy uu____7638))
in ((FStar_Syntax_Const.op_GT), (uu____7632)))
in (

let uu____7650 = (

let uu____7659 = (

let uu____7667 = (

let uu____7673 = (

let uu____7674 = (

let uu____7675 = (

let uu____7678 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7679 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7678), (uu____7679))))
in (FStar_SMTEncoding_Util.mkGTE uu____7675))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7674))
in (quant xy uu____7673))
in ((FStar_Syntax_Const.op_GTE), (uu____7667)))
in (

let uu____7685 = (

let uu____7694 = (

let uu____7702 = (

let uu____7708 = (

let uu____7709 = (

let uu____7710 = (

let uu____7713 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7714 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7713), (uu____7714))))
in (FStar_SMTEncoding_Util.mkSub uu____7710))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7709))
in (quant xy uu____7708))
in ((FStar_Syntax_Const.op_Subtraction), (uu____7702)))
in (

let uu____7720 = (

let uu____7729 = (

let uu____7737 = (

let uu____7743 = (

let uu____7744 = (

let uu____7745 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____7745))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7744))
in (quant qx uu____7743))
in ((FStar_Syntax_Const.op_Minus), (uu____7737)))
in (

let uu____7751 = (

let uu____7760 = (

let uu____7768 = (

let uu____7774 = (

let uu____7775 = (

let uu____7776 = (

let uu____7779 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7780 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7779), (uu____7780))))
in (FStar_SMTEncoding_Util.mkAdd uu____7776))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7775))
in (quant xy uu____7774))
in ((FStar_Syntax_Const.op_Addition), (uu____7768)))
in (

let uu____7786 = (

let uu____7795 = (

let uu____7803 = (

let uu____7809 = (

let uu____7810 = (

let uu____7811 = (

let uu____7814 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7815 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7814), (uu____7815))))
in (FStar_SMTEncoding_Util.mkMul uu____7811))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7810))
in (quant xy uu____7809))
in ((FStar_Syntax_Const.op_Multiply), (uu____7803)))
in (

let uu____7821 = (

let uu____7830 = (

let uu____7838 = (

let uu____7844 = (

let uu____7845 = (

let uu____7846 = (

let uu____7849 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7850 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7849), (uu____7850))))
in (FStar_SMTEncoding_Util.mkDiv uu____7846))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7845))
in (quant xy uu____7844))
in ((FStar_Syntax_Const.op_Division), (uu____7838)))
in (

let uu____7856 = (

let uu____7865 = (

let uu____7873 = (

let uu____7879 = (

let uu____7880 = (

let uu____7881 = (

let uu____7884 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7885 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7884), (uu____7885))))
in (FStar_SMTEncoding_Util.mkMod uu____7881))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7880))
in (quant xy uu____7879))
in ((FStar_Syntax_Const.op_Modulus), (uu____7873)))
in (

let uu____7891 = (

let uu____7900 = (

let uu____7908 = (

let uu____7914 = (

let uu____7915 = (

let uu____7916 = (

let uu____7919 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____7920 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____7919), (uu____7920))))
in (FStar_SMTEncoding_Util.mkAnd uu____7916))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7915))
in (quant xy uu____7914))
in ((FStar_Syntax_Const.op_And), (uu____7908)))
in (

let uu____7926 = (

let uu____7935 = (

let uu____7943 = (

let uu____7949 = (

let uu____7950 = (

let uu____7951 = (

let uu____7954 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____7955 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____7954), (uu____7955))))
in (FStar_SMTEncoding_Util.mkOr uu____7951))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7950))
in (quant xy uu____7949))
in ((FStar_Syntax_Const.op_Or), (uu____7943)))
in (

let uu____7961 = (

let uu____7970 = (

let uu____7978 = (

let uu____7984 = (

let uu____7985 = (

let uu____7986 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____7986))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7985))
in (quant qx uu____7984))
in ((FStar_Syntax_Const.op_Negation), (uu____7978)))
in (uu____7970)::[])
in (uu____7935)::uu____7961))
in (uu____7900)::uu____7926))
in (uu____7865)::uu____7891))
in (uu____7830)::uu____7856))
in (uu____7795)::uu____7821))
in (uu____7760)::uu____7786))
in (uu____7729)::uu____7751))
in (uu____7694)::uu____7720))
in (uu____7659)::uu____7685))
in (uu____7624)::uu____7650))
in (uu____7589)::uu____7615))
in (uu____7554)::uu____7580))
in (uu____7523)::uu____7545))
in (uu____7493)::uu____7514))
in (

let mk = (fun l v -> (

let uu____8114 = (

let uu____8119 = (FStar_All.pipe_right prims (FStar_List.find (fun uu____8151 -> (match (uu____8151) with
| (l', uu____8160) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____8119 (FStar_Option.map (fun uu____8193 -> (match (uu____8193) with
| (uu____8204, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right uu____8114 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun uu____8245 -> (match (uu____8245) with
| (l', uu____8254) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let uu____8277 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____8277) with
| (xxsym, xx) -> begin
(

let uu____8282 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____8282) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let uu____8289 = (

let uu____8294 = (

let uu____8295 = (

let uu____8301 = (

let uu____8302 = (

let uu____8305 = (

let uu____8306 = (

let uu____8309 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____8309)))
in (FStar_SMTEncoding_Util.mkEq uu____8306))
in ((xx_has_type), (uu____8305)))
in (FStar_SMTEncoding_Util.mkImp uu____8302))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____8301)))
in (FStar_SMTEncoding_Util.mkForall uu____8295))
in (

let uu____8322 = (

let uu____8324 = (

let uu____8325 = (

let uu____8326 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "pretyping_" uu____8326))
in (varops.mk_unique uu____8325))
in Some (uu____8324))
in ((uu____8294), (Some ("pretyping")), (uu____8322))))
in FStar_SMTEncoding_Term.Assume (uu____8289))))
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

let uu____8357 = (

let uu____8358 = (

let uu____8363 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____8363), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8358))
in (

let uu____8366 = (

let uu____8368 = (

let uu____8369 = (

let uu____8374 = (

let uu____8375 = (

let uu____8381 = (

let uu____8382 = (

let uu____8385 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____8385)))
in (FStar_SMTEncoding_Util.mkImp uu____8382))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8381)))
in (mkForall_fuel uu____8375))
in ((uu____8374), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8369))
in (uu____8368)::[])
in (uu____8357)::uu____8366))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8414 = (

let uu____8415 = (

let uu____8420 = (

let uu____8421 = (

let uu____8427 = (

let uu____8430 = (

let uu____8432 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____8432)::[])
in (uu____8430)::[])
in (

let uu____8435 = (

let uu____8436 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8436 tt))
in ((uu____8427), ((bb)::[]), (uu____8435))))
in (FStar_SMTEncoding_Util.mkForall uu____8421))
in ((uu____8420), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8415))
in (

let uu____8448 = (

let uu____8450 = (

let uu____8451 = (

let uu____8456 = (

let uu____8457 = (

let uu____8463 = (

let uu____8464 = (

let uu____8467 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (uu____8467)))
in (FStar_SMTEncoding_Util.mkImp uu____8464))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8463)))
in (mkForall_fuel uu____8457))
in ((uu____8456), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8451))
in (uu____8450)::[])
in (uu____8414)::uu____8448))))))
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

let uu____8502 = (

let uu____8503 = (

let uu____8507 = (

let uu____8509 = (

let uu____8511 = (

let uu____8513 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____8514 = (

let uu____8516 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8516)::[])
in (uu____8513)::uu____8514))
in (tt)::uu____8511)
in (tt)::uu____8509)
in (("Prims.Precedes"), (uu____8507)))
in (FStar_SMTEncoding_Util.mkApp uu____8503))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8502))
in (

let precedes_y_x = (

let uu____8519 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8519))
in (

let uu____8521 = (

let uu____8522 = (

let uu____8527 = (

let uu____8528 = (

let uu____8534 = (

let uu____8537 = (

let uu____8539 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8539)::[])
in (uu____8537)::[])
in (

let uu____8542 = (

let uu____8543 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8543 tt))
in ((uu____8534), ((bb)::[]), (uu____8542))))
in (FStar_SMTEncoding_Util.mkForall uu____8528))
in ((uu____8527), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8522))
in (

let uu____8555 = (

let uu____8557 = (

let uu____8558 = (

let uu____8563 = (

let uu____8564 = (

let uu____8570 = (

let uu____8571 = (

let uu____8574 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (uu____8574)))
in (FStar_SMTEncoding_Util.mkImp uu____8571))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8570)))
in (mkForall_fuel uu____8564))
in ((uu____8563), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8558))
in (

let uu____8588 = (

let uu____8590 = (

let uu____8591 = (

let uu____8596 = (

let uu____8597 = (

let uu____8603 = (

let uu____8604 = (

let uu____8607 = (

let uu____8608 = (

let uu____8610 = (

let uu____8612 = (

let uu____8614 = (

let uu____8615 = (

let uu____8618 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____8619 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8618), (uu____8619))))
in (FStar_SMTEncoding_Util.mkGT uu____8615))
in (

let uu____8620 = (

let uu____8622 = (

let uu____8623 = (

let uu____8626 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8627 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8626), (uu____8627))))
in (FStar_SMTEncoding_Util.mkGTE uu____8623))
in (

let uu____8628 = (

let uu____8630 = (

let uu____8631 = (

let uu____8634 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8635 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____8634), (uu____8635))))
in (FStar_SMTEncoding_Util.mkLT uu____8631))
in (uu____8630)::[])
in (uu____8622)::uu____8628))
in (uu____8614)::uu____8620))
in (typing_pred_y)::uu____8612)
in (typing_pred)::uu____8610)
in (FStar_SMTEncoding_Util.mk_and_l uu____8608))
in ((uu____8607), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____8604))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____8603)))
in (mkForall_fuel uu____8597))
in ((uu____8596), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (uu____8591))
in (uu____8590)::[])
in (uu____8557)::uu____8588))
in (uu____8521)::uu____8555)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8666 = (

let uu____8667 = (

let uu____8672 = (

let uu____8673 = (

let uu____8679 = (

let uu____8682 = (

let uu____8684 = (FStar_SMTEncoding_Term.boxString b)
in (uu____8684)::[])
in (uu____8682)::[])
in (

let uu____8687 = (

let uu____8688 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8688 tt))
in ((uu____8679), ((bb)::[]), (uu____8687))))
in (FStar_SMTEncoding_Util.mkForall uu____8673))
in ((uu____8672), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8667))
in (

let uu____8700 = (

let uu____8702 = (

let uu____8703 = (

let uu____8708 = (

let uu____8709 = (

let uu____8715 = (

let uu____8716 = (

let uu____8719 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (uu____8719)))
in (FStar_SMTEncoding_Util.mkImp uu____8716))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8715)))
in (mkForall_fuel uu____8709))
in ((uu____8708), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8703))
in (uu____8702)::[])
in (uu____8666)::uu____8700))))))
in (

let mk_ref = (fun env reft_name uu____8742 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (

let uu____8753 = (

let uu____8757 = (

let uu____8759 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (uu____8759)::[])
in ((reft_name), (uu____8757)))
in (FStar_SMTEncoding_Util.mkApp uu____8753))
in (

let refb = (

let uu____8762 = (

let uu____8766 = (

let uu____8768 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (uu____8768)::[])
in ((reft_name), (uu____8766)))
in (FStar_SMTEncoding_Util.mkApp uu____8762))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (

let uu____8772 = (

let uu____8773 = (

let uu____8778 = (

let uu____8779 = (

let uu____8785 = (

let uu____8786 = (

let uu____8789 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (uu____8789)))
in (FStar_SMTEncoding_Util.mkImp uu____8786))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (uu____8785)))
in (mkForall_fuel uu____8779))
in ((uu____8778), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8773))
in (

let uu____8805 = (

let uu____8807 = (

let uu____8808 = (

let uu____8813 = (

let uu____8814 = (

let uu____8820 = (

let uu____8821 = (

let uu____8824 = (FStar_SMTEncoding_Util.mkAnd ((typing_pred), (typing_pred_b)))
in (

let uu____8825 = (

let uu____8826 = (

let uu____8829 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let uu____8830 = (FStar_SMTEncoding_Util.mkFreeV bb)
in ((uu____8829), (uu____8830))))
in (FStar_SMTEncoding_Util.mkEq uu____8826))
in ((uu____8824), (uu____8825))))
in (FStar_SMTEncoding_Util.mkImp uu____8821))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (uu____8820)))
in (mkForall_fuel' (Prims.parse_int "2") uu____8814))
in ((uu____8813), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (uu____8808))
in (uu____8807)::[])
in (uu____8772)::uu____8805))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), (Some ("true_interp")))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____8874 = (

let uu____8875 = (

let uu____8880 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____8880), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8875))
in (uu____8874)::[])))
in (

let mk_and_interp = (fun env conj uu____8892 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____8902 = (

let uu____8906 = (

let uu____8908 = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (uu____8908)::[])
in (("Valid"), (uu____8906)))
in (FStar_SMTEncoding_Util.mkApp uu____8902))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____8915 = (

let uu____8916 = (

let uu____8921 = (

let uu____8922 = (

let uu____8928 = (

let uu____8929 = (

let uu____8932 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____8932), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____8929))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____8928)))
in (FStar_SMTEncoding_Util.mkForall uu____8922))
in ((uu____8921), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8916))
in (uu____8915)::[])))))))))
in (

let mk_or_interp = (fun env disj uu____8957 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____8967 = (

let uu____8971 = (

let uu____8973 = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (uu____8973)::[])
in (("Valid"), (uu____8971)))
in (FStar_SMTEncoding_Util.mkApp uu____8967))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____8980 = (

let uu____8981 = (

let uu____8986 = (

let uu____8987 = (

let uu____8993 = (

let uu____8994 = (

let uu____8997 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____8997), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____8994))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____8993)))
in (FStar_SMTEncoding_Util.mkForall uu____8987))
in ((uu____8986), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8981))
in (uu____8980)::[])))))))))
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

let uu____9036 = (

let uu____9040 = (

let uu____9042 = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (uu____9042)::[])
in (("Valid"), (uu____9040)))
in (FStar_SMTEncoding_Util.mkApp uu____9036))
in (

let uu____9045 = (

let uu____9046 = (

let uu____9051 = (

let uu____9052 = (

let uu____9058 = (

let uu____9059 = (

let uu____9062 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((uu____9062), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9059))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (uu____9058)))
in (FStar_SMTEncoding_Util.mkForall uu____9052))
in ((uu____9051), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9046))
in (uu____9045)::[])))))))))
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

let uu____9107 = (

let uu____9111 = (

let uu____9113 = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (uu____9113)::[])
in (("Valid"), (uu____9111)))
in (FStar_SMTEncoding_Util.mkApp uu____9107))
in (

let uu____9116 = (

let uu____9117 = (

let uu____9122 = (

let uu____9123 = (

let uu____9129 = (

let uu____9130 = (

let uu____9133 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((uu____9133), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9130))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (uu____9129)))
in (FStar_SMTEncoding_Util.mkForall uu____9123))
in ((uu____9122), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9117))
in (uu____9116)::[])))))))))))
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

let uu____9172 = (

let uu____9176 = (

let uu____9178 = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (uu____9178)::[])
in (("Valid"), (uu____9176)))
in (FStar_SMTEncoding_Util.mkApp uu____9172))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9185 = (

let uu____9186 = (

let uu____9191 = (

let uu____9192 = (

let uu____9198 = (

let uu____9199 = (

let uu____9202 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____9202), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9199))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9198)))
in (FStar_SMTEncoding_Util.mkForall uu____9192))
in ((uu____9191), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9186))
in (uu____9185)::[])))))))))
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

let uu____9237 = (

let uu____9241 = (

let uu____9243 = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (uu____9243)::[])
in (("Valid"), (uu____9241)))
in (FStar_SMTEncoding_Util.mkApp uu____9237))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9250 = (

let uu____9251 = (

let uu____9256 = (

let uu____9257 = (

let uu____9263 = (

let uu____9264 = (

let uu____9267 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____9267), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9264))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9263)))
in (FStar_SMTEncoding_Util.mkForall uu____9257))
in ((uu____9256), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9251))
in (uu____9250)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let valid = (

let uu____9298 = (

let uu____9302 = (

let uu____9304 = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (uu____9304)::[])
in (("Valid"), (uu____9302)))
in (FStar_SMTEncoding_Util.mkApp uu____9298))
in (

let not_valid_a = (

let uu____9308 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9308))
in (

let uu____9310 = (

let uu____9311 = (

let uu____9316 = (

let uu____9317 = (

let uu____9323 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (uu____9323)))
in (FStar_SMTEncoding_Util.mkForall uu____9317))
in ((uu____9316), (Some ("not interpretation")), (Some ("l_not-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9311))
in (uu____9310)::[]))))))
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

let uu____9360 = (

let uu____9364 = (

let uu____9366 = (FStar_SMTEncoding_Util.mkApp ((for_all), ((a)::(b)::[])))
in (uu____9366)::[])
in (("Valid"), (uu____9364)))
in (FStar_SMTEncoding_Util.mkApp uu____9360))
in (

let valid_b_x = (

let uu____9370 = (

let uu____9374 = (

let uu____9376 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (uu____9376)::[])
in (("Valid"), (uu____9374)))
in (FStar_SMTEncoding_Util.mkApp uu____9370))
in (

let uu____9378 = (

let uu____9379 = (

let uu____9384 = (

let uu____9385 = (

let uu____9391 = (

let uu____9392 = (

let uu____9395 = (

let uu____9396 = (

let uu____9402 = (

let uu____9405 = (

let uu____9407 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (uu____9407)::[])
in (uu____9405)::[])
in (

let uu____9410 = (

let uu____9411 = (

let uu____9414 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((uu____9414), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9411))
in ((uu____9402), ((xx)::[]), (uu____9410))))
in (FStar_SMTEncoding_Util.mkForall uu____9396))
in ((uu____9395), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9392))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9391)))
in (FStar_SMTEncoding_Util.mkForall uu____9385))
in ((uu____9384), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9379))
in (uu____9378)::[]))))))))))
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

let uu____9462 = (

let uu____9466 = (

let uu____9468 = (FStar_SMTEncoding_Util.mkApp ((for_some), ((a)::(b)::[])))
in (uu____9468)::[])
in (("Valid"), (uu____9466)))
in (FStar_SMTEncoding_Util.mkApp uu____9462))
in (

let valid_b_x = (

let uu____9472 = (

let uu____9476 = (

let uu____9478 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (uu____9478)::[])
in (("Valid"), (uu____9476)))
in (FStar_SMTEncoding_Util.mkApp uu____9472))
in (

let uu____9480 = (

let uu____9481 = (

let uu____9486 = (

let uu____9487 = (

let uu____9493 = (

let uu____9494 = (

let uu____9497 = (

let uu____9498 = (

let uu____9504 = (

let uu____9507 = (

let uu____9509 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (uu____9509)::[])
in (uu____9507)::[])
in (

let uu____9512 = (

let uu____9513 = (

let uu____9516 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((uu____9516), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9513))
in ((uu____9504), ((xx)::[]), (uu____9512))))
in (FStar_SMTEncoding_Util.mkExists uu____9498))
in ((uu____9497), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9494))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9493)))
in (FStar_SMTEncoding_Util.mkForall uu____9487))
in ((uu____9486), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9481))
in (uu____9480)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____9553 = (

let uu____9554 = (

let uu____9559 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (

let uu____9560 = (

let uu____9562 = (varops.mk_unique "typing_range_const")
in Some (uu____9562))
in ((uu____9559), (Some ("Range_const typing")), (uu____9560))))
in FStar_SMTEncoding_Term.Assume (uu____9554))
in (uu____9553)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (

let uu____9825 = (FStar_Util.find_opt (fun uu____9843 -> (match (uu____9843) with
| (l, uu____9853) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)
in (match (uu____9825) with
| None -> begin
[]
end
| Some (uu____9875, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9912 = (encode_function_type_as_formula None None t env)
in (match (uu____9912) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9945 = ((

let uu____9946 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation uu____9946)) || (FStar_Syntax_Util.is_lemma t_norm))
in (match (uu____9945) with
| true -> begin
(

let uu____9950 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____9950) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (

let uu____9962 = (

let uu____9963 = (FStar_Syntax_Subst.compress t_norm)
in uu____9963.FStar_Syntax_Syntax.n)
in (match (uu____9962) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____9968) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____9985 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____9988 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env)))))
end))
end
| uu____9996 -> begin
(

let uu____9997 = (prims.is lid)
in (match (uu____9997) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____10002 = (prims.mk lid vname)
in (match (uu____10002) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end
| uu____10015 -> begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let uu____10017 = (

let uu____10023 = (curried_arrow_formals_comp t_norm)
in (match (uu____10023) with
| (args, comp) -> begin
(match (encode_non_total_function_typ) with
| true -> begin
(

let uu____10038 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (uu____10038)))
end
| uu____10045 -> begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end)
end))
in (match (uu____10017) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____10065 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____10065) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____10078 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___123_10102 -> (match (uu___123_10102) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____10105 = (FStar_Util.prefix vars)
in (match (uu____10105) with
| (uu____10116, (xxsym, uu____10118)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____10128 = (

let uu____10129 = (

let uu____10134 = (

let uu____10135 = (

let uu____10141 = (

let uu____10142 = (

let uu____10145 = (

let uu____10146 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____10146))
in ((vapp), (uu____10145)))
in (FStar_SMTEncoding_Util.mkEq uu____10142))
in ((((vapp)::[])::[]), (vars), (uu____10141)))
in (FStar_SMTEncoding_Util.mkForall uu____10135))
in ((uu____10134), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (uu____10129))
in (uu____10128)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____10158 = (FStar_Util.prefix vars)
in (match (uu____10158) with
| (uu____10169, (xxsym, uu____10171)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____10185 = (

let uu____10186 = (

let uu____10191 = (

let uu____10192 = (

let uu____10198 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____10198)))
in (FStar_SMTEncoding_Util.mkForall uu____10192))
in ((uu____10191), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (uu____10186))
in (uu____10185)::[])))))
end))
end
| uu____10208 -> begin
[]
end)))))
in (

let uu____10209 = (encode_binders None formals env)
in (match (uu____10209) with
| (vars, guards, env', decls1, uu____10225) -> begin
(

let uu____10232 = (match (pre_opt) with
| None -> begin
(

let uu____10237 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____10237), (decls1)))
end
| Some (p) -> begin
(

let uu____10239 = (encode_formula p env')
in (match (uu____10239) with
| (g, ds) -> begin
(

let uu____10246 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____10246), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____10232) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____10255 = (

let uu____10259 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____10259)))
in (FStar_SMTEncoding_Util.mkApp uu____10255))
in (

let uu____10264 = (

let vname_decl = (

let uu____10269 = (

let uu____10275 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____10280 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____10275), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____10269))
in (

let uu____10285 = (

let env = (

let uu___151_10289 = env
in {bindings = uu___151_10289.bindings; depth = uu___151_10289.depth; tcenv = uu___151_10289.tcenv; warn = uu___151_10289.warn; cache = uu___151_10289.cache; nolabels = uu___151_10289.nolabels; use_zfuel_name = uu___151_10289.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (

let uu____10290 = (

let uu____10291 = (head_normal env tt)
in (not (uu____10291)))
in (match (uu____10290) with
| true -> begin
(encode_term_pred None tt env vtok_tm)
end
| uu____10294 -> begin
(encode_term_pred None t_norm env vtok_tm)
end)))
in (match (uu____10285) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let uu____10303 = (match (formals) with
| [] -> begin
(

let uu____10312 = (

let uu____10313 = (

let uu____10315 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_34 -> Some (_0_34)) uu____10315))
in (push_free_var env lid vname uu____10313))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (uu____10312)))
end
| uu____10318 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (

let uu____10323 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) uu____10323))
in (

let name_tok_corr = (

let uu____10325 = (

let uu____10330 = (

let uu____10331 = (

let uu____10337 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____10337)))
in (FStar_SMTEncoding_Util.mkForall uu____10331))
in ((uu____10330), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (uu____10325))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (uu____10303) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (uu____10264) with
| (decls2, env) -> begin
(

let uu____10362 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let uu____10367 = (encode_term res_t env')
in (match (uu____10367) with
| (encoded_res_t, decls) -> begin
(

let uu____10375 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____10375), (decls)))
end)))
in (match (uu____10362) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____10383 = (

let uu____10388 = (

let uu____10389 = (

let uu____10395 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____10395)))
in (FStar_SMTEncoding_Util.mkForall uu____10389))
in ((uu____10388), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (uu____10383))
in (

let freshness = (

let uu____10405 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____10405) with
| true -> begin
(

let uu____10408 = (

let uu____10409 = (

let uu____10415 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (

let uu____10421 = (varops.next_id ())
in ((vname), (uu____10415), (FStar_SMTEncoding_Term.Term_sort), (uu____10421))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____10409))
in (

let uu____10423 = (

let uu____10425 = (pretype_axiom vapp vars)
in (uu____10425)::[])
in (uu____10408)::uu____10423))
end
| uu____10426 -> begin
[]
end))
in (

let g = (

let uu____10429 = (

let uu____10431 = (

let uu____10433 = (

let uu____10435 = (

let uu____10437 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____10437)
in (FStar_List.append freshness uu____10435))
in (FStar_List.append decls3 uu____10433))
in (FStar_List.append decls2 uu____10431))
in (FStar_List.append decls1 uu____10429))
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

let uu____10459 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10459) with
| None -> begin
(

let uu____10482 = (encode_free_var env x t t_norm [])
in (match (uu____10482) with
| (decls, env) -> begin
(

let uu____10497 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10497) with
| (n, x', uu____10516) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, uu____10528) -> begin
((((n), (x))), ([]), (env))
end)))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let uu____10561 = (encode_free_var env lid t tt quals)
in (match (uu____10561) with
| (decls, env) -> begin
(

let uu____10572 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____10572) with
| true -> begin
(

let uu____10576 = (

let uu____10578 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls uu____10578))
in ((uu____10576), (env)))
end
| uu____10581 -> begin
((decls), (env))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____10606 lb -> (match (uu____10606) with
| (decls, env) -> begin
(

let uu____10618 = (

let uu____10622 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env uu____10622 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____10618) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____10646 quals -> (match (uu____10646) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____10695 = (FStar_Util.first_N nbinders formals)
in (match (uu____10695) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun uu____10735 uu____10736 -> (match (((uu____10735), (uu____10736))) with
| ((formal, uu____10746), (binder, uu____10748)) -> begin
(

let uu____10753 = (

let uu____10758 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____10758)))
in FStar_Syntax_Syntax.NT (uu____10753))
end)) formals binders)
in (

let extra_formals = (

let uu____10763 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____10777 -> (match (uu____10777) with
| (x, i) -> begin
(

let uu____10784 = (

let uu___152_10785 = x
in (

let uu____10786 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___152_10785.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___152_10785.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____10786}))
in ((uu____10784), (i)))
end))))
in (FStar_All.pipe_right uu____10763 FStar_Syntax_Util.name_binders))
in (

let body = (

let uu____10798 = (

let uu____10800 = (

let uu____10801 = (FStar_Syntax_Subst.subst subst t)
in uu____10801.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _0_35 -> Some (_0_35)) uu____10800))
in (

let uu____10805 = (

let uu____10806 = (FStar_Syntax_Subst.compress body)
in (

let uu____10807 = (

let uu____10808 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd uu____10808))
in (FStar_Syntax_Syntax.extend_app_n uu____10806 uu____10807)))
in (uu____10805 uu____10798 body.FStar_Syntax_Syntax.pos)))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (

let uu____10867 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____10867) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____10920)::uu____10921 -> begin
(

let uu____10929 = (

let uu____10930 = (FStar_Syntax_Subst.compress t_norm)
in uu____10930.FStar_Syntax_Syntax.n)
in (match (uu____10929) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____10959 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____10959) with
| (formals, c) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (FStar_Syntax_Util.comp_result c)
in (

let uu____10989 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c))
in (match (uu____10989) with
| true -> begin
(

let uu____11009 = (FStar_Util.first_N nformals binders)
in (match (uu____11009) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun uu____11057 uu____11058 -> (match (((uu____11057), (uu____11058))) with
| ((b, uu____11068), (x, uu____11070)) -> begin
(

let uu____11075 = (

let uu____11080 = (FStar_Syntax_Syntax.bv_to_name x)
in ((b), (uu____11080)))
in FStar_Syntax_Syntax.NT (uu____11075))
end)) bs0 formals)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))), (false))))
end))
end
| uu____11102 -> begin
(match ((nformals > nbinders)) with
| true -> begin
(

let uu____11122 = (eta_expand binders formals body tres)
in (match (uu____11122) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end))
end
| uu____11174 -> begin
((((binders), (body), (formals), (tres))), (false))
end)
end)))))
end))
end
| FStar_Syntax_Syntax.Tm_refine (x, uu____11184) -> begin
(

let uu____11189 = (

let uu____11202 = (aux norm x.FStar_Syntax_Syntax.sort)
in (Prims.fst uu____11202))
in ((uu____11189), (true)))
end
| uu____11241 when (not (norm)) -> begin
(

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
in (aux true t_norm))
end
| uu____11243 -> begin
(

let uu____11244 = (

let uu____11245 = (FStar_Syntax_Print.term_to_string e)
in (

let uu____11246 = (FStar_Syntax_Print.term_to_string t_norm)
in (FStar_Util.format3 "Impossible! let-bound lambda %s = %s has a type that\'s not a function: %s\n" flid.FStar_Ident.str uu____11245 uu____11246)))
in (failwith uu____11244))
end))
end
| uu____11261 -> begin
(

let uu____11262 = (

let uu____11263 = (FStar_Syntax_Subst.compress t_norm)
in uu____11263.FStar_Syntax_Syntax.n)
in (match (uu____11262) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____11292 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____11292) with
| (formals, c) -> begin
(

let tres = (FStar_Syntax_Util.comp_result c)
in (

let uu____11314 = (eta_expand [] formals e tres)
in (match (uu____11314) with
| (binders, body) -> begin
((((binders), (body), (formals), (tres))), (false))
end)))
end))
end
| uu____11368 -> begin
(((([]), (e), ([]), (t_norm))), (false))
end))
end)
end)))
in (aux false t_norm)))
in try
(match (()) with
| () -> begin
(

let uu____11396 = (FStar_All.pipe_right bindings (FStar_Util.for_all (fun lb -> (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp))))
in (match (uu____11396) with
| true -> begin
(encode_top_level_vals env bindings quals)
end
| uu____11402 -> begin
(

let uu____11403 = (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____11444 lb -> (match (uu____11444) with
| (toks, typs, decls, env) -> begin
((

let uu____11495 = (FStar_Syntax_Util.is_lemma lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____11495) with
| true -> begin
(Prims.raise Let_rec_unencodeable)
end
| uu____11496 -> begin
()
end));
(

let t_norm = (whnf env lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____11498 = (

let uu____11506 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (declare_top_level_let env uu____11506 lb.FStar_Syntax_Syntax.lbtyp t_norm))
in (match (uu____11498) with
| (tok, decl, env) -> begin
(

let uu____11531 = (

let uu____11538 = (

let uu____11544 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in ((uu____11544), (tok)))
in (uu____11538)::toks)
in ((uu____11531), ((t_norm)::typs), ((decl)::decls), (env)))
end)));
)
end)) (([]), ([]), ([]), (env))))
in (match (uu____11403) with
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
| uu____11646 -> begin
(match (curry) with
| true -> begin
(match (ftok) with
| Some (ftok) -> begin
(mk_Apply ftok vars)
end
| None -> begin
(

let uu____11651 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____11651 vars))
end)
end
| uu____11652 -> begin
(

let uu____11653 = (

let uu____11657 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____11657)))
in (FStar_SMTEncoding_Util.mkApp uu____11653))
end)
end))
in (

let uu____11662 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___124_11664 -> (match (uu___124_11664) with
| FStar_Syntax_Syntax.HasMaskedEffect -> begin
true
end
| uu____11665 -> begin
false
end)))) || (FStar_All.pipe_right typs (FStar_Util.for_some (fun t -> (

let uu____11668 = (FStar_Syntax_Util.is_pure_or_ghost_function t)
in (FStar_All.pipe_left Prims.op_Negation uu____11668))))))
in (match (uu____11662) with
| true -> begin
((decls), (env))
end
| uu____11673 -> begin
(match ((not (is_rec))) with
| true -> begin
(match (((bindings), (typs), (toks))) with
| (({FStar_Syntax_Syntax.lbname = uu____11688; FStar_Syntax_Syntax.lbunivs = uu____11689; FStar_Syntax_Syntax.lbtyp = uu____11690; FStar_Syntax_Syntax.lbeff = uu____11691; FStar_Syntax_Syntax.lbdef = e})::[], (t_norm)::[], ((flid_fv, (f, ftok)))::[]) -> begin
(

let e = (FStar_Syntax_Subst.compress e)
in (

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____11733 = (destruct_bound_function flid t_norm e)
in (match (uu____11733) with
| ((binders, body, uu____11745, uu____11746), curry) -> begin
(

let uu____11752 = (encode_binders None binders env)
in (match (uu____11752) with
| (vars, guards, env', binder_decls, uu____11768) -> begin
(

let app = (mk_app curry f ftok vars)
in (

let uu____11776 = (

let uu____11781 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____11781) with
| true -> begin
(

let uu____11787 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____11788 = (encode_formula body env')
in ((uu____11787), (uu____11788))))
end
| uu____11793 -> begin
(

let uu____11794 = (encode_term body env')
in ((app), (uu____11794)))
end))
in (match (uu____11776) with
| (app, (body, decls2)) -> begin
(

let eqn = (

let uu____11808 = (

let uu____11813 = (

let uu____11814 = (

let uu____11820 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (uu____11820)))
in (FStar_SMTEncoding_Util.mkForall uu____11814))
in (

let uu____11826 = (

let uu____11828 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (uu____11828))
in ((uu____11813), (uu____11826), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (uu____11808))
in (

let uu____11831 = (

let uu____11833 = (

let uu____11835 = (

let uu____11837 = (

let uu____11839 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) uu____11839))
in (FStar_List.append decls2 uu____11837))
in (FStar_List.append binder_decls uu____11835))
in (FStar_List.append decls uu____11833))
in ((uu____11831), (env))))
end)))
end))
end))))
end
| uu____11842 -> begin
(failwith "Impossible")
end)
end
| uu____11857 -> begin
(

let fuel = (

let uu____11861 = (varops.fresh "fuel")
in ((uu____11861), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env
in (

let uu____11864 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun uu____11903 uu____11904 -> (match (((uu____11903), (uu____11904))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (

let uu____11986 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____11986))
in (

let gtok = (

let uu____11988 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____11988))
in (

let env = (

let uu____11990 = (

let uu____11992 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_36 -> Some (_0_36)) uu____11992))
in (push_free_var env flid gtok uu____11990))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (uu____11864) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 uu____12076 t_norm uu____12078 -> (match (((uu____12076), (uu____12078))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uu____12102; FStar_Syntax_Syntax.lbtyp = uu____12103; FStar_Syntax_Syntax.lbeff = uu____12104; FStar_Syntax_Syntax.lbdef = e}) -> begin
((

let uu____12122 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12122) with
| true -> begin
(

let uu____12123 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____12124 = (FStar_Syntax_Print.term_to_string t_norm)
in (

let uu____12125 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____12123 uu____12124 uu____12125))))
end
| uu____12126 -> begin
()
end));
(

let uu____12127 = (destruct_bound_function flid t_norm e)
in (match (uu____12127) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____12149 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12149) with
| true -> begin
(

let uu____12150 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____12151 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let rec: binders=[%s], body=%s\n" uu____12150 uu____12151)))
end
| uu____12152 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____12154 -> begin
()
end);
(

let uu____12155 = (encode_binders None binders env)
in (match (uu____12155) with
| (vars, guards, env', binder_decls, uu____12173) -> begin
(

let decl_g = (

let uu____12181 = (

let uu____12187 = (

let uu____12189 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____12189)
in ((g), (uu____12187), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____12181))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____12204 = (

let uu____12208 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____12208)))
in (FStar_SMTEncoding_Util.mkApp uu____12204))
in (

let gsapp = (

let uu____12214 = (

let uu____12218 = (

let uu____12220 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____12220)::vars_tm)
in ((g), (uu____12218)))
in (FStar_SMTEncoding_Util.mkApp uu____12214))
in (

let gmax = (

let uu____12224 = (

let uu____12228 = (

let uu____12230 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____12230)::vars_tm)
in ((g), (uu____12228)))
in (FStar_SMTEncoding_Util.mkApp uu____12224))
in (

let uu____12233 = (encode_term body env')
in (match (uu____12233) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____12244 = (

let uu____12249 = (

let uu____12250 = (

let uu____12258 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____12258)))
in (FStar_SMTEncoding_Util.mkForall' uu____12250))
in (

let uu____12269 = (

let uu____12271 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (uu____12271))
in ((uu____12249), (uu____12269), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (uu____12244))
in (

let eqn_f = (

let uu____12275 = (

let uu____12280 = (

let uu____12281 = (

let uu____12287 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____12287)))
in (FStar_SMTEncoding_Util.mkForall uu____12281))
in ((uu____12280), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12275))
in (

let eqn_g' = (

let uu____12296 = (

let uu____12301 = (

let uu____12302 = (

let uu____12308 = (

let uu____12309 = (

let uu____12312 = (

let uu____12313 = (

let uu____12317 = (

let uu____12319 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____12319)::vars_tm)
in ((g), (uu____12317)))
in (FStar_SMTEncoding_Util.mkApp uu____12313))
in ((gsapp), (uu____12312)))
in (FStar_SMTEncoding_Util.mkEq uu____12309))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____12308)))
in (FStar_SMTEncoding_Util.mkForall uu____12302))
in ((uu____12301), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12296))
in (

let uu____12332 = (

let uu____12337 = (encode_binders None formals env0)
in (match (uu____12337) with
| (vars, v_guards, env, binder_decls, uu____12354) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (

let uu____12369 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____12369 ((fuel)::vars)))
in (

let uu____12372 = (

let uu____12377 = (

let uu____12378 = (

let uu____12384 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (uu____12384)))
in (FStar_SMTEncoding_Util.mkForall uu____12378))
in ((uu____12377), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (uu____12372)))
in (

let uu____12396 = (

let uu____12400 = (encode_term_pred None tres env gapp)
in (match (uu____12400) with
| (g_typing, d3) -> begin
(

let uu____12408 = (

let uu____12410 = (

let uu____12411 = (

let uu____12416 = (

let uu____12417 = (

let uu____12423 = (

let uu____12424 = (

let uu____12427 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____12427), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____12424))
in ((((gapp)::[])::[]), ((fuel)::vars), (uu____12423)))
in (FStar_SMTEncoding_Util.mkForall uu____12417))
in ((uu____12416), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12411))
in (uu____12410)::[])
in ((d3), (uu____12408)))
end))
in (match (uu____12396) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____12332) with
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

let uu____12463 = (

let uu____12470 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun uu____12502 uu____12503 -> (match (((uu____12502), (uu____12503))) with
| ((decls, eqns, env0), (gtok, ty, lb)) -> begin
(

let uu____12579 = (encode_one_binding env0 gtok ty lb)
in (match (uu____12579) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) uu____12470))
in (match (uu____12463) with
| (decls, eqns, env0) -> begin
(

let uu____12619 = (

let uu____12624 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right uu____12624 (FStar_List.partition (fun uu___125_12634 -> (match (uu___125_12634) with
| FStar_SMTEncoding_Term.DeclFun (uu____12635) -> begin
true
end
| uu____12641 -> begin
false
end)))))
in (match (uu____12619) with
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

let uu____12659 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____12659 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> ((

let uu____12692 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12692) with
| true -> begin
(

let uu____12693 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") uu____12693))
end
| uu____12694 -> begin
()
end));
(

let nm = (

let uu____12696 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____12696) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____12699 = (encode_sigelt' env se)
in (match (uu____12699) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(

let uu____12708 = (

let uu____12710 = (

let uu____12711 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12711))
in (uu____12710)::[])
in ((uu____12708), (e)))
end
| uu____12713 -> begin
(

let uu____12714 = (

let uu____12716 = (

let uu____12718 = (

let uu____12719 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12719))
in (uu____12718)::g)
in (

let uu____12720 = (

let uu____12722 = (

let uu____12723 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12723))
in (uu____12722)::[])
in (FStar_List.append uu____12716 uu____12720)))
in ((uu____12714), (e)))
end)
end)));
))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____12731) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, uu____12742) -> begin
(

let uu____12743 = (

let uu____12744 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____12744 Prims.op_Negation))
in (match (uu____12743) with
| true -> begin
(([]), (env))
end
| uu____12749 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____12764 -> begin
(

let uu____12765 = (

let uu____12768 = (

let uu____12769 = (

let uu____12784 = (FStar_All.pipe_left (fun _0_37 -> Some (_0_37)) (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (uu____12784)))
in FStar_Syntax_Syntax.Tm_abs (uu____12769))
in (FStar_Syntax_Syntax.mk uu____12768))
in (uu____12765 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env a -> (

let uu____12837 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (uu____12837) with
| (aname, atok, env) -> begin
(

let uu____12847 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____12847) with
| (formals, uu____12857) -> begin
(

let uu____12864 = (

let uu____12867 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____12867 env))
in (match (uu____12864) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____12875 = (

let uu____12876 = (

let uu____12882 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____12890 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____12882), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____12876))
in (uu____12875)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let uu____12897 = (

let uu____12904 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____12924 -> (match (uu____12924) with
| (bv, uu____12932) -> begin
(

let uu____12933 = (gen_term_var env bv)
in (match (uu____12933) with
| (xxsym, xx, uu____12943) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right uu____12904 FStar_List.split))
in (match (uu____12897) with
| (xs_sorts, xs) -> begin
(

let app = (

let uu____12973 = (

let uu____12977 = (

let uu____12979 = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (uu____12979)::[])
in (("Reify"), (uu____12977)))
in (FStar_SMTEncoding_Util.mkApp uu____12973))
in (

let a_eq = (

let uu____12983 = (

let uu____12988 = (

let uu____12989 = (

let uu____12995 = (

let uu____12996 = (

let uu____12999 = (mk_Apply tm xs_sorts)
in ((app), (uu____12999)))
in (FStar_SMTEncoding_Util.mkEq uu____12996))
in ((((app)::[])::[]), (xs_sorts), (uu____12995)))
in (FStar_SMTEncoding_Util.mkForall uu____12989))
in ((uu____12988), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (uu____12983))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____13012 = (

let uu____13017 = (

let uu____13018 = (

let uu____13024 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____13024)))
in (FStar_SMTEncoding_Util.mkForall uu____13018))
in ((uu____13017), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (uu____13012))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____13035 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____13035) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13051, uu____13052, uu____13053, uu____13054) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let uu____13057 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____13057) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13068, t, quals, uu____13071) -> begin
(

let will_encode_definition = (

let uu____13075 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___126_13077 -> (match (uu___126_13077) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| uu____13080 -> begin
false
end))))
in (not (uu____13075)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____13084 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____13086 = (encode_top_level_val env fv t quals)
in (match (uu____13086) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____13098 = (

let uu____13100 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls uu____13100))
in ((uu____13098), (env)))))
end)))
end))
end
| FStar_Syntax_Syntax.Sig_assume (l, f, uu____13105, uu____13106) -> begin
(

let uu____13109 = (encode_formula f env)
in (match (uu____13109) with
| (f, decls) -> begin
(

let g = (

let uu____13118 = (

let uu____13119 = (

let uu____13124 = (

let uu____13126 = (

let uu____13127 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____13127))
in Some (uu____13126))
in (

let uu____13128 = (

let uu____13130 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (uu____13130))
in ((f), (uu____13124), (uu____13128))))
in FStar_SMTEncoding_Term.Assume (uu____13119))
in (uu____13118)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, uu____13136, quals, uu____13138) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let uu____13146 = (FStar_Util.fold_map (fun env lb -> (

let lid = (

let uu____13153 = (

let uu____13158 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____13158.FStar_Syntax_Syntax.fv_name)
in uu____13153.FStar_Syntax_Syntax.v)
in (

let uu____13162 = (

let uu____13163 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____13163))
in (match (uu____13162) with
| true -> begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let uu____13182 = (encode_sigelt' env val_decl)
in (match (uu____13182) with
| (decls, env) -> begin
((env), (decls))
end)))
end
| uu____13189 -> begin
((env), ([]))
end)))) env (Prims.snd lbs))
in (match (uu____13146) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____13199, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = uu____13201; FStar_Syntax_Syntax.lbtyp = uu____13202; FStar_Syntax_Syntax.lbeff = uu____13203; FStar_Syntax_Syntax.lbdef = uu____13204})::[]), uu____13205, uu____13206, uu____13207, uu____13208) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let uu____13224 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____13224) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid_b2t_x = (

let uu____13242 = (

let uu____13246 = (

let uu____13248 = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (uu____13248)::[])
in (("Valid"), (uu____13246)))
in (FStar_SMTEncoding_Util.mkApp uu____13242))
in (

let decls = (

let uu____13253 = (

let uu____13255 = (

let uu____13256 = (

let uu____13261 = (

let uu____13262 = (

let uu____13268 = (

let uu____13269 = (

let uu____13272 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (uu____13272)))
in (FStar_SMTEncoding_Util.mkEq uu____13269))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (uu____13268)))
in (FStar_SMTEncoding_Util.mkForall uu____13262))
in ((uu____13261), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (uu____13256))
in (uu____13255)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::uu____13253)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____13290, uu____13291, uu____13292, quals, uu____13294) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___127_13302 -> (match (uu___127_13302) with
| FStar_Syntax_Syntax.Discriminator (uu____13303) -> begin
true
end
| uu____13304 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____13306, uu____13307, lids, quals, uu____13310) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____13319 = (

let uu____13320 = (FStar_List.hd l.FStar_Ident.ns)
in uu____13320.FStar_Ident.idText)
in (uu____13319 = "Prims"))))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___128_13322 -> (match (uu___128_13322) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____13323 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____13326, uu____13327, quals, uu____13329) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___129_13341 -> (match (uu___129_13341) with
| FStar_Syntax_Syntax.Projector (uu____13342) -> begin
true
end
| uu____13345 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____13352 = (try_lookup_free_var env l)
in (match (uu____13352) with
| Some (uu____13356) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, (lb)::[]), uu____13365, uu____13366, quals, uu____13368) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let uu____13380 = (

let uu____13381 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in uu____13381.FStar_Syntax_Syntax.n)
in (match (uu____13380) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____13388) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let uu____13445 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____13445) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let uu___155_13462 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___155_13462.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___155_13462.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___155_13462.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___155_13462.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___155_13462.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___155_13462.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___155_13462.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___155_13462.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___155_13462.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___155_13462.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___155_13462.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___155_13462.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___155_13462.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___155_13462.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___155_13462.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___155_13462.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___155_13462.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___155_13462.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___155_13462.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___155_13462.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___155_13462.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___155_13462.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___155_13462.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (

let uu____13463 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals uu____13463)))
end))
in (

let lb = (

let uu___156_13467 = lb
in {FStar_Syntax_Syntax.lbname = uu___156_13467.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___156_13467.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = uu___156_13467.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in ((

let uu____13469 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____13469) with
| true -> begin
(

let uu____13470 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____13471 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____13472 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print3 "%s: Reified %s\nto %s\n" uu____13470 uu____13471 uu____13472))))
end
| uu____13473 -> begin
()
end));
(encode_top_level_let env ((is_rec), ((lb)::[])) quals);
))))))
end
| uu____13475 -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____13479, uu____13480, quals, uu____13482) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____13496, uu____13497, uu____13498) -> begin
(

let uu____13505 = (encode_signature env ses)
in (match (uu____13505) with
| (g, env) -> begin
(

let uu____13515 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___130_13525 -> (match (uu___130_13525) with
| FStar_SMTEncoding_Term.Assume (uu____13526, Some ("inversion axiom"), uu____13527) -> begin
false
end
| uu____13531 -> begin
true
end))))
in (match (uu____13515) with
| (g', inversions) -> begin
(

let uu____13540 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___131_13550 -> (match (uu___131_13550) with
| FStar_SMTEncoding_Term.DeclFun (uu____13551) -> begin
true
end
| uu____13557 -> begin
false
end))))
in (match (uu____13540) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____13568, tps, k, uu____13571, datas, quals, uu____13574) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___132_13583 -> (match (uu___132_13583) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| uu____13584 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____13607 = c
in (match (uu____13607) with
| (name, args, uu____13619, uu____13620, uu____13621) -> begin
(

let uu____13628 = (

let uu____13629 = (

let uu____13635 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (uu____13635), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____13629))
in (uu____13628)::[])
end))
end
| uu____13645 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____13660 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____13663 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____13663 FStar_Option.isNone)))))
in (match (uu____13660) with
| true -> begin
[]
end
| uu____13673 -> begin
(

let uu____13674 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13674) with
| (xxsym, xx) -> begin
(

let uu____13680 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____13691 l -> (match (uu____13691) with
| (out, decls) -> begin
(

let uu____13703 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____13703) with
| (uu____13709, data_t) -> begin
(

let uu____13711 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____13711) with
| (args, res) -> begin
(

let indices = (

let uu____13740 = (

let uu____13741 = (FStar_Syntax_Subst.compress res)
in uu____13741.FStar_Syntax_Syntax.n)
in (match (uu____13740) with
| FStar_Syntax_Syntax.Tm_app (uu____13749, indices) -> begin
indices
end
| uu____13765 -> begin
[]
end))
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env uu____13777 -> (match (uu____13777) with
| (x, uu____13781) -> begin
(

let uu____13782 = (

let uu____13783 = (

let uu____13787 = (mk_term_projector_name l x)
in ((uu____13787), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____13783))
in (push_term_var env x uu____13782))
end)) env))
in (

let uu____13789 = (encode_args indices env)
in (match (uu____13789) with
| (indices, decls') -> begin
((match (((FStar_List.length indices) <> (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____13807 -> begin
()
end);
(

let eqs = (

let uu____13809 = (FStar_List.map2 (fun v a -> (

let uu____13817 = (

let uu____13820 = (FStar_SMTEncoding_Util.mkFreeV v)
in ((uu____13820), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____13817))) vars indices)
in (FStar_All.pipe_right uu____13809 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____13822 = (

let uu____13823 = (

let uu____13826 = (

let uu____13827 = (

let uu____13830 = (mk_data_tester env l xx)
in ((uu____13830), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____13827))
in ((out), (uu____13826)))
in (FStar_SMTEncoding_Util.mkOr uu____13823))
in ((uu____13822), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____13680) with
| (data_ax, decls) -> begin
(

let uu____13838 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____13838) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____13849 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____13849 xx tapp))
end
| uu____13851 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____13852 = (

let uu____13857 = (

let uu____13858 = (

let uu____13864 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____13872 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____13864), (uu____13872))))
in (FStar_SMTEncoding_Util.mkForall uu____13858))
in (

let uu____13880 = (

let uu____13882 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (uu____13882))
in ((uu____13857), (Some ("inversion axiom")), (uu____13880))))
in FStar_SMTEncoding_Term.Assume (uu____13852)))
in (

let pattern_guarded_inversion = (

let uu____13887 = ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1")))
in (match (uu____13887) with
| true -> begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (

let uu____13895 = (

let uu____13896 = (

let uu____13901 = (

let uu____13902 = (

let uu____13908 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____13916 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (uu____13908), (uu____13916))))
in (FStar_SMTEncoding_Util.mkForall uu____13902))
in (

let uu____13924 = (

let uu____13926 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (uu____13926))
in ((uu____13901), (Some ("inversion axiom")), (uu____13924))))
in FStar_SMTEncoding_Term.Assume (uu____13896))
in (uu____13895)::[])))
end
| uu____13929 -> begin
[]
end))
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)))
in (

let uu____13930 = (

let uu____13938 = (

let uu____13939 = (FStar_Syntax_Subst.compress k)
in uu____13939.FStar_Syntax_Syntax.n)
in (match (uu____13938) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____13968 -> begin
((tps), (k))
end))
in (match (uu____13930) with
| (formals, res) -> begin
(

let uu____13983 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____13983) with
| (formals, res) -> begin
(

let uu____13990 = (encode_binders None formals env)
in (match (uu____13990) with
| (vars, guards, env', binder_decls, uu____14005) -> begin
(

let uu____14012 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____14012) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____14025 = (

let uu____14029 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____14029)))
in (FStar_SMTEncoding_Util.mkApp uu____14025))
in (

let uu____14034 = (

let tname_decl = (

let uu____14040 = (

let uu____14049 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____14061 -> (match (uu____14061) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (

let uu____14068 = (varops.next_id ())
in ((tname), (uu____14049), (FStar_SMTEncoding_Term.Term_sort), (uu____14068), (false))))
in (constructor_or_logic_type_decl uu____14040))
in (

let uu____14072 = (match (vars) with
| [] -> begin
(

let uu____14079 = (

let uu____14080 = (

let uu____14082 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_38 -> Some (_0_38)) uu____14082))
in (push_free_var env t tname uu____14080))
in (([]), (uu____14079)))
end
| uu____14086 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (

let uu____14092 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____14092))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____14101 = (

let uu____14106 = (

let uu____14107 = (

let uu____14115 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (uu____14115)))
in (FStar_SMTEncoding_Util.mkForall' uu____14107))
in ((uu____14106), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14101))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (uu____14072) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (uu____14034) with
| (decls, env) -> begin
(

let kindingAx = (

let uu____14139 = (encode_term_pred None res env' tapp)
in (match (uu____14139) with
| (k, decls) -> begin
(

let karr = (match (((FStar_List.length formals) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____14153 = (

let uu____14154 = (

let uu____14159 = (

let uu____14160 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____14160))
in ((uu____14159), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14154))
in (uu____14153)::[])
end
| uu____14163 -> begin
[]
end)
in (

let uu____14164 = (

let uu____14166 = (

let uu____14168 = (

let uu____14169 = (

let uu____14174 = (

let uu____14175 = (

let uu____14181 = (FStar_SMTEncoding_Util.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (uu____14181)))
in (FStar_SMTEncoding_Util.mkForall uu____14175))
in ((uu____14174), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14169))
in (uu____14168)::[])
in (FStar_List.append karr uu____14166))
in (FStar_List.append decls uu____14164)))
end))
in (

let aux = (

let uu____14191 = (

let uu____14193 = (inversion_axioms tapp vars)
in (

let uu____14195 = (

let uu____14197 = (pretype_axiom tapp vars)
in (uu____14197)::[])
in (FStar_List.append uu____14193 uu____14195)))
in (FStar_List.append kindingAx uu____14191))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14202, uu____14203, uu____14204, uu____14205, uu____14206, uu____14207, uu____14208) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14215, t, uu____14217, n_tps, quals, uu____14220, drange) -> begin
(

let uu____14226 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____14226) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____14237 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____14237) with
| (formals, t_res) -> begin
(

let uu____14259 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____14259) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____14268 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____14268) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (

let uu____14301 = (mk_term_projector_name d x)
in ((uu____14301), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (

let uu____14303 = (

let uu____14312 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (uu____14312), (true)))
in (FStar_All.pipe_right uu____14303 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____14332 = (encode_term_pred None t env ddtok_tm)
in (match (uu____14332) with
| (tok_typing, decls3) -> begin
(

let uu____14339 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____14339) with
| (vars', guards', env'', decls_formals, uu____14354) -> begin
(

let uu____14361 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (uu____14361) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____14380 -> begin
(

let uu____14384 = (

let uu____14385 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____14385))
in (uu____14384)::[])
end)
in (

let encode_elim = (fun uu____14392 -> (

let uu____14393 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____14393) with
| (head, args) -> begin
(

let uu____14422 = (

let uu____14423 = (FStar_Syntax_Subst.compress head)
in uu____14423.FStar_Syntax_Syntax.n)
in (match (uu____14422) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____14441 = (encode_args args env')
in (match (uu____14441) with
| (encoded_args, arg_decls) -> begin
(

let uu____14452 = (FStar_List.fold_left (fun uu____14463 arg -> (match (uu____14463) with
| (env, arg_vars, eqns) -> begin
(

let uu____14482 = (

let uu____14486 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env uu____14486))
in (match (uu____14482) with
| (uu____14492, xv, env) -> begin
(

let uu____14495 = (

let uu____14497 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____14497)::eqns)
in ((env), ((xv)::arg_vars), (uu____14495)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (uu____14452) with
| (uu____14505, arg_vars, eqns) -> begin
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

let uu____14526 = (

let uu____14531 = (

let uu____14532 = (

let uu____14538 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14544 = (

let uu____14545 = (

let uu____14548 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (uu____14548)))
in (FStar_SMTEncoding_Util.mkImp uu____14545))
in ((((ty_pred)::[])::[]), (uu____14538), (uu____14544))))
in (FStar_SMTEncoding_Util.mkForall uu____14532))
in ((uu____14531), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (uu____14526))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____14562 = (varops.fresh "x")
in ((uu____14562), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____14564 = (

let uu____14569 = (

let uu____14570 = (

let uu____14576 = (

let uu____14579 = (

let uu____14581 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in (uu____14581)::[])
in (uu____14579)::[])
in (

let uu____14584 = (

let uu____14585 = (

let uu____14588 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____14589 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in ((uu____14588), (uu____14589))))
in (FStar_SMTEncoding_Util.mkImp uu____14585))
in ((uu____14576), ((x)::[]), (uu____14584))))
in (FStar_SMTEncoding_Util.mkForall uu____14570))
in (

let uu____14599 = (

let uu____14601 = (varops.mk_unique "lextop")
in Some (uu____14601))
in ((uu____14569), (Some ("lextop is top")), (uu____14599))))
in FStar_SMTEncoding_Term.Assume (uu____14564))))
end
| uu____14604 -> begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(

let uu____14615 = (

let uu____14616 = (FStar_SMTEncoding_Util.mkFreeV v)
in (FStar_SMTEncoding_Util.mk_Precedes uu____14616 dapp))
in (uu____14615)::[])
end
| uu____14617 -> begin
(failwith "unexpected sort")
end))))
in (

let uu____14619 = (

let uu____14624 = (

let uu____14625 = (

let uu____14631 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14637 = (

let uu____14638 = (

let uu____14641 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____14641)))
in (FStar_SMTEncoding_Util.mkImp uu____14638))
in ((((ty_pred)::[])::[]), (uu____14631), (uu____14637))))
in (FStar_SMTEncoding_Util.mkForall uu____14625))
in ((uu____14624), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (uu____14619)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| uu____14652 -> begin
((

let uu____14654 = (

let uu____14655 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____14656 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____14655 uu____14656)))
in (FStar_Errors.warn drange uu____14654));
(([]), ([]));
)
end))
end)))
in (

let uu____14659 = (encode_elim ())
in (match (uu____14659) with
| (decls2, elim) -> begin
(

let g = (

let uu____14671 = (

let uu____14673 = (

let uu____14675 = (

let uu____14677 = (

let uu____14679 = (

let uu____14680 = (

let uu____14686 = (

let uu____14688 = (

let uu____14689 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____14689))
in Some (uu____14688))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____14686)))
in FStar_SMTEncoding_Term.DeclFun (uu____14680))
in (uu____14679)::[])
in (

let uu____14692 = (

let uu____14694 = (

let uu____14696 = (

let uu____14698 = (

let uu____14700 = (

let uu____14702 = (

let uu____14704 = (

let uu____14705 = (

let uu____14710 = (

let uu____14711 = (

let uu____14717 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____14717)))
in (FStar_SMTEncoding_Util.mkForall uu____14711))
in ((uu____14710), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (uu____14705))
in (

let uu____14725 = (

let uu____14727 = (

let uu____14728 = (

let uu____14733 = (

let uu____14734 = (

let uu____14740 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____14746 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____14740), (uu____14746))))
in (FStar_SMTEncoding_Util.mkForall uu____14734))
in ((uu____14733), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (uu____14728))
in (uu____14727)::[])
in (uu____14704)::uu____14725))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::uu____14702)
in (FStar_List.append uu____14700 elim))
in (FStar_List.append decls_pred uu____14698))
in (FStar_List.append decls_formals uu____14696))
in (FStar_List.append proxy_fresh uu____14694))
in (FStar_List.append uu____14677 uu____14692)))
in (FStar_List.append decls3 uu____14675))
in (FStar_List.append decls2 uu____14673))
in (FStar_List.append binder_decls uu____14671))
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
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____14769 se -> (match (uu____14769) with
| (g, env) -> begin
(

let uu____14781 = (encode_sigelt env se)
in (match (uu____14781) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____14817 -> (match (uu____14817) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____14835) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____14840 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____14840) with
| true -> begin
(

let uu____14841 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14842 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14843 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____14841 uu____14842 uu____14843))))
end
| uu____14844 -> begin
()
end));
(

let uu____14845 = (encode_term t1 env)
in (match (uu____14845) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____14855 = (

let uu____14859 = (

let uu____14860 = (

let uu____14861 = (FStar_Util.digest_of_string t_hash)
in (

let uu____14862 = (

let uu____14863 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____14863))
in (Prims.strcat uu____14861 uu____14862)))
in (Prims.strcat "x_" uu____14860))
in (new_term_constant_from_string env x uu____14859))
in (match (uu____14855) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = (

let uu____14874 = (FStar_Options.log_queries ())
in (match (uu____14874) with
| true -> begin
(

let uu____14876 = (

let uu____14877 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14878 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14879 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____14877 uu____14878 uu____14879))))
in Some (uu____14876))
end
| uu____14880 -> begin
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
| FStar_TypeChecker_Env.Binding_lid (x, (uu____14892, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____14901 = (encode_free_var env fv t t_norm [])
in (match (uu____14901) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let uu____14920 = (encode_sigelt env se)
in (match (uu____14920) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____14930 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____14930) with
| (uu____14942, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun uu____14987 -> (match (uu____14987) with
| (l, uu____14994, uu____14995) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____15016 -> (match (uu____15016) with
| (l, uu____15024, uu____15025) -> begin
(

let uu____15030 = (FStar_All.pipe_left (fun _0_39 -> FStar_SMTEncoding_Term.Echo (_0_39)) (Prims.fst l))
in (

let uu____15031 = (

let uu____15033 = (

let uu____15034 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____15034))
in (uu____15033)::[])
in (uu____15030)::uu____15031))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____15045 = (

let uu____15047 = (

let uu____15048 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____15048; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (uu____15047)::[])
in (FStar_ST.write last_env uu____15045)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (

let uu____15066 = (FStar_ST.read last_env)
in (match (uu____15066) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____15072 -> begin
(

let uu___157_15074 = e
in {bindings = uu___157_15074.bindings; depth = uu___157_15074.depth; tcenv = tcenv; warn = uu___157_15074.warn; cache = uu___157_15074.cache; nolabels = uu___157_15074.nolabels; use_zfuel_name = uu___157_15074.use_zfuel_name; encode_non_total_function_typ = uu___157_15074.encode_non_total_function_typ})
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____15078 = (FStar_ST.read last_env)
in (match (uu____15078) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____15083)::tl -> begin
(FStar_ST.write last_env ((env)::tl))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____15091 -> (

let uu____15092 = (FStar_ST.read last_env)
in (match (uu____15092) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd)::tl -> begin
(

let refs = (FStar_Util.smap_copy hd.cache)
in (

let top = (

let uu___158_15113 = hd
in {bindings = uu___158_15113.bindings; depth = uu___158_15113.depth; tcenv = uu___158_15113.tcenv; warn = uu___158_15113.warn; cache = refs; nolabels = uu___158_15113.nolabels; use_zfuel_name = uu___158_15113.use_zfuel_name; encode_non_total_function_typ = uu___158_15113.encode_non_total_function_typ})
in (FStar_ST.write last_env ((top)::(hd)::tl))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____15119 -> (

let uu____15120 = (FStar_ST.read last_env)
in (match (uu____15120) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____15125)::tl -> begin
(FStar_ST.write last_env tl)
end)))


let mark_env : Prims.unit  ->  Prims.unit = (fun uu____15133 -> (push_env ()))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15136 -> (pop_env ()))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15139 -> (

let uu____15140 = (FStar_ST.read last_env)
in (match (uu____15140) with
| (hd)::(uu____15146)::tl -> begin
(FStar_ST.write last_env ((hd)::tl))
end
| uu____15152 -> begin
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

let uu____15197 = (FStar_Options.log_queries ())
in (match (uu____15197) with
| true -> begin
(

let uu____15199 = (

let uu____15200 = (

let uu____15201 = (

let uu____15202 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____15202 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____15201))
in FStar_SMTEncoding_Term.Caption (uu____15200))
in (uu____15199)::decls)
end
| uu____15207 -> begin
decls
end)))
in (

let env = (get_env tcenv)
in (

let uu____15209 = (encode_sigelt env se)
in (match (uu____15209) with
| (decls, env) -> begin
((set_env env);
(

let uu____15215 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____15215));
)
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____15224 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____15226 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15226) with
| true -> begin
(

let uu____15227 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____15227))
end
| uu____15230 -> begin
()
end));
(

let env = (get_env tcenv)
in (

let uu____15232 = (encode_signature (

let uu___159_15236 = env
in {bindings = uu___159_15236.bindings; depth = uu___159_15236.depth; tcenv = uu___159_15236.tcenv; warn = false; cache = uu___159_15236.cache; nolabels = uu___159_15236.nolabels; use_zfuel_name = uu___159_15236.use_zfuel_name; encode_non_total_function_typ = uu___159_15236.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____15232) with
| (decls, env) -> begin
(

let caption = (fun decls -> (

let uu____15248 = (FStar_Options.log_queries ())
in (match (uu____15248) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____15251 -> begin
decls
end)))
in ((set_env (

let uu___160_15253 = env
in {bindings = uu___160_15253.bindings; depth = uu___160_15253.depth; tcenv = uu___160_15253.tcenv; warn = true; cache = uu___160_15253.cache; nolabels = uu___160_15253.nolabels; use_zfuel_name = uu___160_15253.use_zfuel_name; encode_non_total_function_typ = uu___160_15253.encode_non_total_function_typ}));
(

let uu____15255 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15255) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____15256 -> begin
()
end));
(

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls));
))
end)));
)))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____15290 = (

let uu____15291 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____15291.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____15290));
(

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____15299 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____15320 = (aux rest)
in (match (uu____15320) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let uu____15336 = (

let uu____15338 = (FStar_Syntax_Syntax.mk_binder (

let uu___161_15339 = x
in {FStar_Syntax_Syntax.ppname = uu___161_15339.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___161_15339.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (uu____15338)::out)
in ((uu____15336), (rest))))
end))
end
| uu____15342 -> begin
(([]), (bindings))
end))
in (

let uu____15346 = (aux bindings)
in (match (uu____15346) with
| (closing, bindings) -> begin
(

let uu____15360 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((uu____15360), (bindings)))
end)))
in (match (uu____15299) with
| (q, bindings) -> begin
(

let uu____15373 = (

let uu____15376 = (FStar_List.filter (fun uu___133_15378 -> (match (uu___133_15378) with
| FStar_TypeChecker_Env.Binding_sig (uu____15379) -> begin
false
end
| uu____15383 -> begin
true
end)) bindings)
in (encode_env_bindings env uu____15376))
in (match (uu____15373) with
| (env_decls, env) -> begin
((

let uu____15394 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____15394) with
| true -> begin
(

let uu____15395 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____15395))
end
| uu____15396 -> begin
()
end));
(

let uu____15397 = (encode_formula q env)
in (match (uu____15397) with
| (phi, qdecls) -> begin
(

let uu____15409 = (

let uu____15412 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____15412 phi))
in (match (uu____15409) with
| (labels, phi) -> begin
(

let uu____15422 = (encode_labels labels)
in (match (uu____15422) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____15443 = (

let uu____15448 = (FStar_SMTEncoding_Util.mkNot phi)
in (

let uu____15449 = (

let uu____15451 = (varops.mk_unique "@query")
in Some (uu____15451))
in ((uu____15448), (Some ("query")), (uu____15449))))
in FStar_SMTEncoding_Term.Assume (uu____15443))
in (

let suffix = (

let uu____15456 = (

let uu____15458 = (

let uu____15460 = (FStar_Options.print_z3_statistics ())
in (match (uu____15460) with
| true -> begin
(FStar_SMTEncoding_Term.PrintStats)::[]
end
| uu____15462 -> begin
[]
end))
in (FStar_List.append uu____15458 ((FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in (FStar_List.append label_suffix uu____15456))
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

let uu____15473 = (encode_formula q env)
in (match (uu____15473) with
| (f, uu____15477) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____15479) -> begin
true
end
| uu____15482 -> begin
false
end);
)
end));
)))





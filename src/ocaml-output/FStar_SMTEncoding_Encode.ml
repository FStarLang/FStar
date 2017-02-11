
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

let a2 = (unmangle a)
in (

let uu____1092 = (aux a2)
in (match (uu____1092) with
| None -> begin
(

let uu____1098 = (

let uu____1099 = (FStar_Syntax_Print.bv_to_string a2)
in (

let uu____1100 = (print_env env)
in (FStar_Util.format2 "Bound term variable not found (after unmangling): %s in environment: %s" uu____1099 uu____1100)))
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

let uu____1120 = (

let uu___140_1121 = env
in (

let uu____1122 = (

let uu____1124 = (

let uu____1125 = (

let uu____1132 = (

let uu____1134 = (FStar_SMTEncoding_Util.mkApp ((ftok), ([])))
in (FStar_All.pipe_left (fun _0_29 -> Some (_0_29)) uu____1134))
in ((x), (fname), (uu____1132), (None)))
in Binding_fvar (uu____1125))
in (uu____1124)::env.bindings)
in {bindings = uu____1122; depth = uu___140_1121.depth; tcenv = uu___140_1121.tcenv; warn = uu___140_1121.warn; cache = uu___140_1121.cache; nolabels = uu___140_1121.nolabels; use_zfuel_name = uu___140_1121.use_zfuel_name; encode_non_total_function_typ = uu___140_1121.encode_non_total_function_typ}))
in ((fname), (ftok), (uu____1120))))))


let try_lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) Prims.option = (fun env a -> (lookup_binding env (fun uu___112_1156 -> (match (uu___112_1156) with
| Binding_fvar (b, t1, t2, t3) when (FStar_Ident.lid_equals b a) -> begin
Some (((t1), (t2), (t3)))
end
| uu____1178 -> begin
None
end))))


let contains_name : env_t  ->  Prims.string  ->  Prims.bool = (fun env s -> (

let uu____1190 = (lookup_binding env (fun uu___113_1192 -> (match (uu___113_1192) with
| Binding_fvar (b, t1, t2, t3) when (b.FStar_Ident.str = s) -> begin
Some (())
end
| uu____1202 -> begin
None
end)))
in (FStar_All.pipe_right uu____1190 FStar_Option.isSome)))


let lookup_lid : env_t  ->  FStar_Ident.lident  ->  (Prims.string * FStar_SMTEncoding_Term.term Prims.option * FStar_SMTEncoding_Term.term Prims.option) = (fun env a -> (

let uu____1215 = (try_lookup_lid env a)
in (match (uu____1215) with
| None -> begin
(

let uu____1232 = (

let uu____1233 = (FStar_Syntax_Print.lid_to_string a)
in (FStar_Util.format1 "Name not found: %s" uu____1233))
in (failwith uu____1232))
end
| Some (s) -> begin
s
end)))


let push_free_var : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option  ->  env_t = (fun env x fname ftok -> (

let uu___141_1264 = env
in {bindings = (Binding_fvar (((x), (fname), (ftok), (None))))::env.bindings; depth = uu___141_1264.depth; tcenv = uu___141_1264.tcenv; warn = uu___141_1264.warn; cache = uu___141_1264.cache; nolabels = uu___141_1264.nolabels; use_zfuel_name = uu___141_1264.use_zfuel_name; encode_non_total_function_typ = uu___141_1264.encode_non_total_function_typ}))


let push_zfuel_name : env_t  ->  FStar_Ident.lident  ->  Prims.string  ->  env_t = (fun env x f -> (

let uu____1276 = (lookup_lid env x)
in (match (uu____1276) with
| (t1, t2, uu____1284) -> begin
(

let t3 = (

let uu____1290 = (

let uu____1294 = (

let uu____1296 = (FStar_SMTEncoding_Util.mkApp (("ZFuel"), ([])))
in (uu____1296)::[])
in ((f), (uu____1294)))
in (FStar_SMTEncoding_Util.mkApp uu____1290))
in (

let uu___142_1299 = env
in {bindings = (Binding_fvar (((x), (t1), (t2), (Some (t3)))))::env.bindings; depth = uu___142_1299.depth; tcenv = uu___142_1299.tcenv; warn = uu___142_1299.warn; cache = uu___142_1299.cache; nolabels = uu___142_1299.nolabels; use_zfuel_name = uu___142_1299.use_zfuel_name; encode_non_total_function_typ = uu___142_1299.encode_non_total_function_typ}))
end)))


let try_lookup_free_var : env_t  ->  FStar_Ident.lident  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env l -> (

let uu____1309 = (try_lookup_lid env l)
in (match (uu____1309) with
| None -> begin
None
end
| Some (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some (f) when env.use_zfuel_name -> begin
Some (f)
end
| uu____1336 -> begin
(match (sym) with
| Some (t) -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____1341, (fuel)::[]) -> begin
(

let uu____1344 = (

let uu____1345 = (

let uu____1346 = (FStar_SMTEncoding_Term.fv_of_term fuel)
in (FStar_All.pipe_right uu____1346 Prims.fst))
in (FStar_Util.starts_with uu____1345 "fuel"))
in (match (uu____1344) with
| true -> begin
(

let uu____1348 = (

let uu____1349 = (FStar_SMTEncoding_Util.mkFreeV ((name), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Term.mk_ApplyTF uu____1349 fuel))
in (FStar_All.pipe_left (fun _0_30 -> Some (_0_30)) uu____1348))
end
| uu____1351 -> begin
Some (t)
end))
end
| uu____1352 -> begin
Some (t)
end)
end
| uu____1353 -> begin
None
end)
end)
end)))


let lookup_free_var = (fun env a -> (

let uu____1371 = (try_lookup_free_var env a.FStar_Syntax_Syntax.v)
in (match (uu____1371) with
| Some (t) -> begin
t
end
| None -> begin
(

let uu____1374 = (

let uu____1375 = (FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v)
in (FStar_Util.format1 "Name not found: %s" uu____1375))
in (failwith uu____1374))
end)))


let lookup_free_var_name = (fun env a -> (

let uu____1392 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____1392) with
| (x, uu____1399, uu____1400) -> begin
x
end)))


let lookup_free_var_sym = (fun env a -> (

let uu____1424 = (lookup_lid env a.FStar_Syntax_Syntax.v)
in (match (uu____1424) with
| (name, sym, zf_opt) -> begin
(match (zf_opt) with
| Some ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g, zf); FStar_SMTEncoding_Term.freevars = uu____1445; FStar_SMTEncoding_Term.rng = uu____1446}) when env.use_zfuel_name -> begin
((g), (zf))
end
| uu____1454 -> begin
(match (sym) with
| None -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end
| Some (sym) -> begin
(match (sym.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (g, (fuel)::[]) -> begin
((g), ((fuel)::[]))
end
| uu____1468 -> begin
((FStar_SMTEncoding_Term.Var (name)), ([]))
end)
end)
end)
end)))


let tok_of_name : env_t  ->  Prims.string  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env nm -> (FStar_Util.find_map env.bindings (fun uu___114_1477 -> (match (uu___114_1477) with
| Binding_fvar (uu____1479, nm', tok, uu____1482) when (nm = nm') -> begin
tok
end
| uu____1487 -> begin
None
end))))


let mkForall_fuel' = (fun n uu____1504 -> (match (uu____1504) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____1520 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____1523 = (FStar_Options.unthrottle_inductives ())
in (match (uu____1523) with
| true -> begin
(fallback ())
end
| uu____1524 -> begin
(

let uu____1525 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____1525) with
| (fsym, fterm) -> begin
(

let add_fuel = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____1544 -> begin
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

let uu____1558 = (add_fuel guards)
in (FStar_SMTEncoding_Util.mk_and_l uu____1558))
end
| uu____1560 -> begin
(

let uu____1561 = (add_fuel ((guard)::[]))
in (FStar_All.pipe_right uu____1561 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard), (body'))))
end
| uu____1564 -> begin
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

let uu____1608 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____1608 FStar_Option.isNone))
end
| uu____1621 -> begin
false
end)))


let head_redex : env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____1628 = (

let uu____1629 = (FStar_Syntax_Util.un_uinst t)
in uu____1629.FStar_Syntax_Syntax.n)
in (match (uu____1628) with
| FStar_Syntax_Syntax.Tm_abs (uu____1632, uu____1633, Some (FStar_Util.Inr (l, flags))) -> begin
(((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___115_1662 -> (match (uu___115_1662) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____1663 -> begin
false
end)) flags))
end
| FStar_Syntax_Syntax.Tm_abs (uu____1664, uu____1665, Some (FStar_Util.Inl (lc))) -> begin
(FStar_Syntax_Util.is_tot_or_gtot_lcomp lc)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____1692 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____1692 FStar_Option.isSome))
end
| uu____1705 -> begin
false
end)))


let whnf : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____1712 = (head_normal env t)
in (match (uu____1712) with
| true -> begin
t
end
| uu____1713 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t)
end)))


let norm : env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____1723 = (

let uu____1727 = (FStar_Syntax_Syntax.null_binder t)
in (uu____1727)::[])
in (

let uu____1728 = (FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Util.abs uu____1723 uu____1728 None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((Prims.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(

let uu____1755 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out uu____1755))
end
| s -> begin
(

let uu____1758 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out uu____1758))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___116_1770 -> (match (uu___116_1770) with
| (FStar_SMTEncoding_Term.Var ("ApplyTT")) | (FStar_SMTEncoding_Term.Var ("ApplyTF")) -> begin
true
end
| uu____1771 -> begin
false
end))


let is_eta : env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.option = (fun env vars t -> (

let rec aux = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____1799; FStar_SMTEncoding_Term.rng = uu____1800})::[]), (x)::xs) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(aux f xs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____1814) -> begin
(

let uu____1819 = (((FStar_List.length args) = (FStar_List.length vars)) && (FStar_List.forall2 (fun a v -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v)
end
| uu____1829 -> begin
false
end)) args vars))
in (match (uu____1819) with
| true -> begin
(tok_of_name env f)
end
| uu____1831 -> begin
None
end))
end
| (uu____1832, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____1835 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (

let uu____1837 = (FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)
in (not (uu____1837))))))
in (match (uu____1835) with
| true -> begin
Some (t)
end
| uu____1839 -> begin
None
end)))
end
| uu____1840 -> begin
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
| uu____1924 -> begin
false
end))


let encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Term.term = (fun uu___117_1927 -> (match (uu___117_1927) with
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

let uu____1929 = (

let uu____1933 = (

let uu____1935 = (

let uu____1936 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c))
in (FStar_SMTEncoding_Term.boxInt uu____1936))
in (uu____1935)::[])
in (("FStar.Char.Char"), (uu____1933)))
in (FStar_SMTEncoding_Util.mkApp uu____1929))
end
| FStar_Const.Const_int (i, None) -> begin
(

let uu____1944 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____1944))
end
| FStar_Const.Const_int (i, Some (uu____1946)) -> begin
(failwith "Machine integers should be desugared")
end
| FStar_Const.Const_string (bytes, uu____1955) -> begin
(

let uu____1958 = (FStar_All.pipe_left FStar_Util.string_of_bytes bytes)
in (varops.string_const uu____1958))
end
| FStar_Const.Const_range (r) -> begin
FStar_SMTEncoding_Term.mk_Range_const
end
| FStar_Const.Const_effect -> begin
FStar_SMTEncoding_Term.mk_Term_type
end
| c -> begin
(

let uu____1962 = (

let uu____1963 = (FStar_Syntax_Print.const_to_string c)
in (FStar_Util.format1 "Unhandled constant: %s" uu____1963))
in (failwith uu____1962))
end))


let as_function_typ : env_t  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm t -> (

let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1982) -> begin
t
end
| FStar_Syntax_Syntax.Tm_refine (uu____1990) -> begin
(

let uu____1995 = (FStar_Syntax_Util.unrefine t)
in (aux true uu____1995))
end
| uu____1996 -> begin
(match (norm) with
| true -> begin
(

let uu____1997 = (whnf env t)
in (aux false uu____1997))
end
| uu____1998 -> begin
(

let uu____1999 = (

let uu____2000 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____2001 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____2000 uu____2001)))
in (failwith uu____1999))
end)
end)))
in (aux true t0)))


let curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k = (FStar_Syntax_Subst.compress k)
in (match (k.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| uu____2022 -> begin
(

let uu____2023 = (FStar_Syntax_Syntax.mk_Total k)
in (([]), (uu____2023)))
end)))


let rec encode_binders : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.binders  ->  env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____2166 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____2166) with
| true -> begin
(

let uu____2167 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____2167))
end
| uu____2168 -> begin
()
end));
(

let uu____2169 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____2205 b -> (match (uu____2205) with
| (vars, guards, env, decls, names) -> begin
(

let uu____2248 = (

let x = (unmangle (Prims.fst b))
in (

let uu____2257 = (gen_term_var env x)
in (match (uu____2257) with
| (xxsym, xx, env') -> begin
(

let uu____2271 = (

let uu____2274 = (norm env x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____2274 env xx))
in (match (uu____2271) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____2248) with
| (v, g, env, decls', n) -> begin
(((v)::vars), ((g)::guards), (env), ((FStar_List.append decls decls')), ((n)::names))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____2169) with
| (vars, guards, env, decls, names) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env), (decls), ((FStar_List.rev names)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2362 = (encode_term t env)
in (match (uu____2362) with
| (t, decls) -> begin
(

let uu____2369 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t)
in ((uu____2369), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2377 = (encode_term t env)
in (match (uu____2377) with
| (t, decls) -> begin
(match (fuel_opt) with
| None -> begin
(

let uu____2386 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t)
in ((uu____2386), (decls)))
end
| Some (f) -> begin
(

let uu____2388 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t)
in ((uu____2388), (decls)))
end)
end)))
and encode_term : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____2395 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____2395) with
| true -> begin
(

let uu____2396 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____2397 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____2398 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____2396 uu____2397 uu____2398))))
end
| uu____2399 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(

let uu____2403 = (

let uu____2404 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____2405 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____2406 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____2407 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2404 uu____2405 uu____2406 uu____2407)))))
in (failwith uu____2403))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____2411 = (

let uu____2412 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____2412))
in (failwith uu____2411))
end
| FStar_Syntax_Syntax.Tm_ascribed (t, k, uu____2417) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_meta (t, uu____2437) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t = (lookup_term_var env x)
in ((t), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v) -> begin
(

let uu____2446 = (lookup_free_var env v.FStar_Syntax_Syntax.fv_name)
in ((uu____2446), ([])))
end
| FStar_Syntax_Syntax.Tm_type (uu____2452) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t, uu____2455) -> begin
(encode_term t env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(

let uu____2461 = (encode_const c)
in ((uu____2461), ([])))
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____2475 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____2475) with
| (binders, res) -> begin
(

let uu____2482 = ((env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____2482) with
| true -> begin
(

let uu____2485 = (encode_binders None binders env)
in (match (uu____2485) with
| (vars, guards, env', decls, uu____2500) -> begin
(

let fsym = (

let uu____2510 = (varops.fresh "f")
in ((uu____2510), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____2513 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___143_2517 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___143_2517.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___143_2517.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___143_2517.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___143_2517.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___143_2517.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___143_2517.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___143_2517.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___143_2517.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___143_2517.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___143_2517.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___143_2517.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___143_2517.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___143_2517.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___143_2517.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___143_2517.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___143_2517.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___143_2517.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___143_2517.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___143_2517.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___143_2517.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___143_2517.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___143_2517.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___143_2517.FStar_TypeChecker_Env.qname_and_index}) res)
in (match (uu____2513) with
| (pre_opt, res_t) -> begin
(

let uu____2524 = (encode_term_pred None res_t env' app)
in (match (uu____2524) with
| (res_pred, decls') -> begin
(

let uu____2531 = (match (pre_opt) with
| None -> begin
(

let uu____2538 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____2538), ([])))
end
| Some (pre) -> begin
(

let uu____2541 = (encode_formula pre env')
in (match (uu____2541) with
| (guard, decls0) -> begin
(

let uu____2549 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____2549), (decls0)))
end))
end)
in (match (uu____2531) with
| (guards, guard_decls) -> begin
(

let t_interp = (

let uu____2557 = (

let uu____2563 = (FStar_SMTEncoding_Util.mkImp ((guards), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____2563)))
in (FStar_SMTEncoding_Util.mkForall uu____2557))
in (

let cvars = (

let uu____2573 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____2573 (FStar_List.filter (fun uu____2579 -> (match (uu____2579) with
| (x, uu____2583) -> begin
(x <> (Prims.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____2594 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____2594) with
| Some (t', sorts, uu____2610) -> begin
(

let uu____2620 = (

let uu____2621 = (

let uu____2625 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t'), (uu____2625)))
in (FStar_SMTEncoding_Util.mkApp uu____2621))
in ((uu____2620), ([])))
end
| None -> begin
(

let tsym = (

let uu____2641 = (

let uu____2642 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____2642))
in (varops.mk_unique uu____2641))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let caption = (

let uu____2649 = (FStar_Options.log_queries ())
in (match (uu____2649) with
| true -> begin
(

let uu____2651 = (FStar_TypeChecker_Normalize.term_to_string env.tcenv t0)
in Some (uu____2651))
end
| uu____2652 -> begin
None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t = (

let uu____2657 = (

let uu____2661 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____2661)))
in (FStar_SMTEncoding_Util.mkApp uu____2657))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = Some ((Prims.strcat "kinding_" tsym))
in (

let uu____2670 = (

let uu____2675 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____2675), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2670)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t)
in (

let pre_typing = (

let a_name = Some ((Prims.strcat "pre_typing_" tsym))
in (

let uu____2690 = (

let uu____2695 = (

let uu____2696 = (

let uu____2702 = (

let uu____2703 = (

let uu____2706 = (

let uu____2707 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____2707))
in ((f_has_t), (uu____2706)))
in (FStar_SMTEncoding_Util.mkImp uu____2703))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____2702)))
in (mkForall_fuel uu____2696))
in ((uu____2695), (Some ("pre-typing for functions")), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2690)))
in (

let t_interp = (

let a_name = Some ((Prims.strcat "interpretation_" tsym))
in (

let uu____2722 = (

let uu____2727 = (

let uu____2728 = (

let uu____2734 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____2734)))
in (FStar_SMTEncoding_Util.mkForall uu____2728))
in ((uu____2727), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2722)))
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
| uu____2757 -> begin
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

let uu____2767 = (

let uu____2772 = (FStar_SMTEncoding_Term.mk_HasType t FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____2772), (Some ("Typing for non-total arrows")), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2767)))
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

let uu____2783 = (

let uu____2788 = (

let uu____2789 = (

let uu____2795 = (

let uu____2796 = (

let uu____2799 = (

let uu____2800 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____2800))
in ((f_has_t), (uu____2799)))
in (FStar_SMTEncoding_Util.mkImp uu____2796))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____2795)))
in (mkForall_fuel uu____2789))
in ((uu____2788), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____2783)))
in ((t), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_refine (uu____2815) -> begin
(

let uu____2820 = (

let uu____2823 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t0)
in (match (uu____2823) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.tk = uu____2828; FStar_Syntax_Syntax.pos = uu____2829; FStar_Syntax_Syntax.vars = uu____2830} -> begin
(

let uu____2837 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) f)
in (match (uu____2837) with
| (b, f) -> begin
(

let uu____2851 = (

let uu____2852 = (FStar_List.hd b)
in (Prims.fst uu____2852))
in ((uu____2851), (f)))
end))
end
| uu____2857 -> begin
(failwith "impossible")
end))
in (match (uu____2820) with
| (x, f) -> begin
(

let uu____2864 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____2864) with
| (base_t, decls) -> begin
(

let uu____2871 = (gen_term_var env x)
in (match (uu____2871) with
| (x, xtm, env') -> begin
(

let uu____2880 = (encode_formula f env')
in (match (uu____2880) with
| (refinement, decls') -> begin
(

let uu____2887 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____2887) with
| (fsym, fterm) -> begin
(

let encoding = (

let uu____2895 = (

let uu____2898 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (Some (fterm)) xtm base_t)
in ((uu____2898), (refinement)))
in (FStar_SMTEncoding_Util.mkAnd uu____2895))
in (

let cvars = (

let uu____2903 = (FStar_SMTEncoding_Term.free_variables encoding)
in (FStar_All.pipe_right uu____2903 (FStar_List.filter (fun uu____2909 -> (match (uu____2909) with
| (y, uu____2913) -> begin
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

let uu____2932 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____2932) with
| Some (t, uu____2947, uu____2948) -> begin
(

let uu____2958 = (

let uu____2959 = (

let uu____2963 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((t), (uu____2963)))
in (FStar_SMTEncoding_Util.mkApp uu____2959))
in ((uu____2958), ([])))
end
| None -> begin
(

let tsym = (

let uu____2979 = (

let uu____2980 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_refine_" uu____2980))
in (varops.mk_unique uu____2979))
in (

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let t = (

let uu____2989 = (

let uu____2993 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____2993)))
in (FStar_SMTEncoding_Util.mkApp uu____2989))
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

let uu____3003 = (

let uu____3008 = (

let uu____3009 = (

let uu____3015 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars), (uu____3015)))
in (FStar_SMTEncoding_Util.mkForall uu____3009))
in ((uu____3008), (Some ((Prims.strcat "haseq for " tsym))), (Some ((Prims.strcat "haseq" tsym)))))
in FStar_SMTEncoding_Term.Assume (uu____3003))
in (

let t_kinding = (

let uu____3026 = (

let uu____3031 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____3031), (Some ("refinement kinding")), (Some ((Prims.strcat "refinement_kinding_" tsym)))))
in FStar_SMTEncoding_Term.Assume (uu____3026))
in (

let t_interp = (

let uu____3042 = (

let uu____3047 = (

let uu____3048 = (

let uu____3054 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars), (uu____3054)))
in (FStar_SMTEncoding_Util.mkForall uu____3048))
in (

let uu____3066 = (

let uu____3068 = (FStar_Syntax_Print.term_to_string t0)
in Some (uu____3068))
in ((uu____3047), (uu____3066), (Some ((Prims.strcat "refinement_interpretation_" tsym))))))
in FStar_SMTEncoding_Term.Assume (uu____3042))
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

let uu____3097 = (FStar_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____3097))
in (

let uu____3101 = (encode_term_pred None k env ttm)
in (match (uu____3101) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____3109 = (

let uu____3114 = (

let uu____3116 = (

let uu____3117 = (

let uu____3118 = (

let uu____3119 = (FStar_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____3119))
in (FStar_Util.format1 "uvar_typing_%s" uu____3118))
in (varops.mk_unique uu____3117))
in Some (uu____3116))
in ((t_has_k), (Some ("Uvar typing")), (uu____3114)))
in FStar_SMTEncoding_Term.Assume (uu____3109))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____3126) -> begin
(

let uu____3136 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____3136) with
| (head, args_e) -> begin
(

let uu____3164 = (

let uu____3172 = (

let uu____3173 = (FStar_Syntax_Subst.compress head)
in uu____3173.FStar_Syntax_Syntax.n)
in ((uu____3172), (args_e)))
in (match (uu____3164) with
| (uu____3183, uu____3184) when (head_redex env head) -> begin
(

let uu____3195 = (whnf env t)
in (encode_term uu____3195 env))
end
| ((FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), (_)::((v1, _))::((v2, _))::[])) | ((FStar_Syntax_Syntax.Tm_fvar (fv), (_)::((v1, _))::((v2, _))::[])) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.lexcons_lid) -> begin
(

let uu____3269 = (encode_term v1 env)
in (match (uu____3269) with
| (v1, decls1) -> begin
(

let uu____3276 = (encode_term v2 env)
in (match (uu____3276) with
| (v2, decls2) -> begin
(

let uu____3283 = (FStar_SMTEncoding_Util.mk_LexCons v1 v2)
in ((uu____3283), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____3285) -> begin
(

let e0 = (

let uu____3299 = (

let uu____3302 = (

let uu____3303 = (

let uu____3313 = (

let uu____3319 = (FStar_List.hd args_e)
in (uu____3319)::[])
in ((head), (uu____3313)))
in FStar_Syntax_Syntax.Tm_app (uu____3303))
in (FStar_Syntax_Syntax.mk uu____3302))
in (uu____3299 None head.FStar_Syntax_Syntax.pos))
in ((

let uu____3352 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____3352) with
| true -> begin
(

let uu____3353 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Trying to normalize %s\n" uu____3353))
end
| uu____3354 -> begin
()
end));
(

let e0 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv e0)
in ((

let uu____3357 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____3357) with
| true -> begin
(

let uu____3358 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" uu____3358))
end
| uu____3359 -> begin
()
end));
(

let e0 = (

let uu____3361 = (

let uu____3362 = (

let uu____3363 = (FStar_Syntax_Subst.compress e0)
in uu____3363.FStar_Syntax_Syntax.n)
in (match (uu____3362) with
| FStar_Syntax_Syntax.Tm_app (uu____3366) -> begin
false
end
| uu____3376 -> begin
true
end))
in (match (uu____3361) with
| true -> begin
e0
end
| uu____3377 -> begin
(

let uu____3378 = (FStar_Syntax_Util.head_and_args e0)
in (match (uu____3378) with
| (head, args) -> begin
(

let uu____3404 = (

let uu____3405 = (

let uu____3406 = (FStar_Syntax_Subst.compress head)
in uu____3406.FStar_Syntax_Syntax.n)
in (match (uu____3405) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify) -> begin
true
end
| uu____3409 -> begin
false
end))
in (match (uu____3404) with
| true -> begin
(match (args) with
| (x)::[] -> begin
(Prims.fst x)
end
| uu____3425 -> begin
(failwith "Impossible : Reify applied to multiple arguments after normalization.")
end)
end
| uu____3431 -> begin
e0
end))
end))
end))
in (

let e = (match (args_e) with
| (uu____3433)::[] -> begin
e0
end
| uu____3446 -> begin
(

let uu____3452 = (

let uu____3455 = (

let uu____3456 = (

let uu____3466 = (FStar_List.tl args_e)
in ((e0), (uu____3466)))
in FStar_Syntax_Syntax.Tm_app (uu____3456))
in (FStar_Syntax_Syntax.mk uu____3455))
in (uu____3452 None t0.FStar_Syntax_Syntax.pos))
end)
in (encode_term e env)));
));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____3489)), ((arg, uu____3491))::[]) -> begin
(encode_term arg env)
end
| uu____3509 -> begin
(

let uu____3517 = (encode_args args_e env)
in (match (uu____3517) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____3550 = (encode_term head env)
in (match (uu____3550) with
| (head, decls') -> begin
(

let app_tm = (mk_Apply_args head args)
in (match (ht_opt) with
| None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| Some (formals, c) -> begin
(

let uu____3589 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____3589) with
| (formals, rest) -> begin
(

let subst = (FStar_List.map2 (fun uu____3631 uu____3632 -> (match (((uu____3631), (uu____3632))) with
| ((bv, uu____3646), (a, uu____3648)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals args_e)
in (

let ty = (

let uu____3662 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____3662 (FStar_Syntax_Subst.subst subst)))
in (

let uu____3667 = (encode_term_pred None ty env app_tm)
in (match (uu____3667) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____3677 = (

let uu____3682 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____3687 = (

let uu____3689 = (

let uu____3690 = (

let uu____3691 = (

let uu____3692 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____3692))
in (Prims.strcat "partial_app_typing_" uu____3691))
in (varops.mk_unique uu____3690))
in Some (uu____3689))
in ((uu____3682), (Some ("Partial app typing")), (uu____3687))))
in FStar_SMTEncoding_Term.Assume (uu____3677))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____3710 = (lookup_free_var_sym env fv)
in (match (uu____3710) with
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

let uu____3748 = (

let uu____3749 = (FStar_TypeChecker_Env.lookup_lid env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____3749 Prims.snd))
in Some (uu____3748))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3758, FStar_Util.Inl (t), uu____3760) -> begin
Some (t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3781, FStar_Util.Inr (c), uu____3783) -> begin
Some ((FStar_Syntax_Util.comp_result c))
end
| uu____3804 -> begin
None
end)
in (match (head_type) with
| None -> begin
(encode_partial_app None)
end
| Some (head_type) -> begin
(

let head_type = (

let uu____3824 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv head_type)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____3824))
in (

let uu____3825 = (curried_arrow_formals_comp head_type)
in (match (uu____3825) with
| (formals, c) -> begin
(match (head.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) when ((FStar_List.length formals) = (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____3850 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (Some (((formals), (c)))))
end
| uu____3862 -> begin
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

let uu____3895 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____3895) with
| (bs, body, opening) -> begin
(

let fallback = (fun uu____3910 -> (

let f = (varops.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Imprecise function encoding"))))
in (

let uu____3915 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____3915), ((decl)::[]))))))
in (

let is_impure = (fun uu___118_3925 -> (match (uu___118_3925) with
| FStar_Util.Inl (lc) -> begin
(

let uu____3935 = (FStar_Syntax_Util.is_pure_or_ghost_lcomp lc)
in (not (uu____3935)))
end
| FStar_Util.Inr (eff, uu____3937) -> begin
(

let uu____3943 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv eff)
in (FStar_All.pipe_right uu____3943 Prims.op_Negation))
end))
in (

let codomain_eff = (fun lc -> (match (lc) with
| FStar_Util.Inl (lc) -> begin
(

let uu____3964 = (

let uu____3965 = (lc.FStar_Syntax_Syntax.comp ())
in (FStar_Syntax_Subst.subst_comp opening uu____3965))
in (FStar_All.pipe_right uu____3964 (fun _0_31 -> Some (_0_31))))
end
| FStar_Util.Inr (eff, flags) -> begin
(

let new_uvar = (fun uu____3977 -> (

let uu____3978 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____3978 Prims.fst)))
in (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(

let uu____3986 = (

let uu____3987 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_Total uu____3987))
in (FStar_All.pipe_right uu____3986 (fun _0_32 -> Some (_0_32))))
end
| uu____3989 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(

let uu____3991 = (

let uu____3992 = (new_uvar ())
in (FStar_Syntax_Syntax.mk_GTotal uu____3992))
in (FStar_All.pipe_right uu____3991 (fun _0_33 -> Some (_0_33))))
end
| uu____3994 -> begin
None
end)
end))
end))
in (match (lopt) with
| None -> begin
((

let uu____4003 = (

let uu____4004 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____4004))
in (FStar_Errors.warn t0.FStar_Syntax_Syntax.pos uu____4003));
(fallback ());
)
end
| Some (lc) -> begin
(

let uu____4016 = (is_impure lc)
in (match (uu____4016) with
| true -> begin
(fallback ())
end
| uu____4019 -> begin
(

let uu____4020 = (encode_binders None bs env)
in (match (uu____4020) with
| (vars, guards, envbody, decls, uu____4035) -> begin
(

let uu____4042 = (encode_term body envbody)
in (match (uu____4042) with
| (body, decls') -> begin
(

let key_body = (

let uu____4050 = (

let uu____4056 = (

let uu____4057 = (

let uu____4060 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____4060), (body)))
in (FStar_SMTEncoding_Util.mkImp uu____4057))
in (([]), (vars), (uu____4056)))
in (FStar_SMTEncoding_Util.mkForall uu____4050))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____4071 = (FStar_Util.smap_try_find env.cache tkey_hash)
in (match (uu____4071) with
| Some (t, uu____4086, uu____4087) -> begin
(

let uu____4097 = (

let uu____4098 = (

let uu____4102 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((t), (uu____4102)))
in (FStar_SMTEncoding_Util.mkApp uu____4098))
in ((uu____4097), ([])))
end
| None -> begin
(

let uu____4113 = (is_eta env vars body)
in (match (uu____4113) with
| Some (t) -> begin
((t), ([]))
end
| None -> begin
(

let cvar_sorts = (FStar_List.map Prims.snd cvars)
in (

let fsym = (

let uu____4124 = (

let uu____4125 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____4125))
in (varops.mk_unique uu____4124))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let f = (

let uu____4130 = (

let uu____4134 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((fsym), (uu____4134)))
in (FStar_SMTEncoding_Util.mkApp uu____4130))
in (

let app = (mk_Apply f vars)
in (

let typing_f = (

let uu____4142 = (codomain_eff lc)
in (match (uu____4142) with
| None -> begin
[]
end
| Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs c)
in (

let uu____4149 = (encode_term_pred None tfun env f)
in (match (uu____4149) with
| (f_has_t, decls'') -> begin
(

let a_name = Some ((Prims.strcat "typing_" fsym))
in (

let uu____4157 = (

let uu____4159 = (

let uu____4160 = (

let uu____4165 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars), (f_has_t)))
in ((uu____4165), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____4160))
in (uu____4159)::[])
in (FStar_List.append decls'' uu____4157)))
end)))
end))
in (

let interp_f = (

let a_name = Some ((Prims.strcat "interpretation_" fsym))
in (

let uu____4175 = (

let uu____4180 = (

let uu____4181 = (

let uu____4187 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars)), (uu____4187)))
in (FStar_SMTEncoding_Util.mkForall uu____4181))
in ((uu____4180), (a_name), (a_name)))
in FStar_SMTEncoding_Term.Assume (uu____4175)))
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
| FStar_Syntax_Syntax.Tm_let ((uu____4206, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____4207); FStar_Syntax_Syntax.lbunivs = uu____4208; FStar_Syntax_Syntax.lbtyp = uu____4209; FStar_Syntax_Syntax.lbeff = uu____4210; FStar_Syntax_Syntax.lbdef = uu____4211})::uu____4212), uu____4213) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____4231; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____4233; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____4249) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(

let e = (varops.fresh "let-rec")
in (

let decl_e = FStar_SMTEncoding_Term.DeclFun (((e), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let uu____4262 = (FStar_SMTEncoding_Util.mkFreeV ((e), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____4262), ((decl_e)::[])))));
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____4304 = (encode_term e1 env)
in (match (uu____4304) with
| (ee1, decls1) -> begin
(

let uu____4311 = (FStar_Syntax_Subst.open_term ((((x), (None)))::[]) e2)
in (match (uu____4311) with
| (xs, e2) -> begin
(

let uu____4325 = (FStar_List.hd xs)
in (match (uu____4325) with
| (x, uu____4333) -> begin
(

let env' = (push_term_var env x ee1)
in (

let uu____4335 = (encode_body e2 env')
in (match (uu____4335) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  env_t  ->  (FStar_Syntax_Syntax.term  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____4357 = (

let uu____4361 = (

let uu____4362 = ((FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown) None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_bv uu____4362))
in (gen_term_var env uu____4361))
in (match (uu____4357) with
| (scrsym, scr', env) -> begin
(

let uu____4376 = (encode_term e env)
in (match (uu____4376) with
| (scr, decls) -> begin
(

let uu____4383 = (

let encode_branch = (fun b uu____4399 -> (match (uu____4399) with
| (else_case, decls) -> begin
(

let uu____4410 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____4410) with
| (p, w, br) -> begin
(

let patterns = (encode_pat env p)
in (FStar_List.fold_right (fun uu____4440 uu____4441 -> (match (((uu____4440), (uu____4441))) with
| ((env0, pattern), (else_case, decls)) -> begin
(

let guard = (pattern.guard scr')
in (

let projections = (pattern.projections scr')
in (

let env = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env uu____4478 -> (match (uu____4478) with
| (x, t) -> begin
(push_term_var env x t)
end)) env))
in (

let uu____4483 = (match (w) with
| None -> begin
((guard), ([]))
end
| Some (w) -> begin
(

let uu____4498 = (encode_term w env)
in (match (uu____4498) with
| (w, decls2) -> begin
(

let uu____4506 = (

let uu____4507 = (

let uu____4510 = (

let uu____4511 = (

let uu____4514 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w), (uu____4514)))
in (FStar_SMTEncoding_Util.mkEq uu____4511))
in ((guard), (uu____4510)))
in (FStar_SMTEncoding_Util.mkAnd uu____4507))
in ((uu____4506), (decls2)))
end))
end)
in (match (uu____4483) with
| (guard, decls2) -> begin
(

let uu____4522 = (encode_br br env)
in (match (uu____4522) with
| (br, decls3) -> begin
(

let uu____4530 = (FStar_SMTEncoding_Util.mkITE ((guard), (br), (else_case)))
in ((uu____4530), ((FStar_List.append decls (FStar_List.append decls2 decls3)))))
end))
end)))))
end)) patterns ((else_case), (decls))))
end))
end))
in (FStar_List.fold_right encode_branch pats ((default_case), (decls))))
in (match (uu____4383) with
| (match_tm, decls) -> begin
(

let uu____4542 = (FStar_SMTEncoding_Term.mkLet' (((((((scrsym), (FStar_SMTEncoding_Term.Term_sort))), (scr)))::[]), (match_tm)) FStar_Range.dummyRange)
in ((uu____4542), (decls)))
end))
end))
end)))
and encode_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) Prims.list = (fun env pat -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (ps) -> begin
(FStar_List.map (encode_one_pat env) ps)
end
| uu____4573 -> begin
(

let uu____4574 = (encode_one_pat env pat)
in (uu____4574)::[])
end))
and encode_one_pat : env_t  ->  FStar_Syntax_Syntax.pat  ->  (env_t * pattern) = (fun env pat -> ((

let uu____4586 = (FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low)
in (match (uu____4586) with
| true -> begin
(

let uu____4587 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____4587))
end
| uu____4588 -> begin
()
end));
(

let uu____4589 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____4589) with
| (vars, pat_term) -> begin
(

let uu____4599 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____4622 v -> (match (uu____4622) with
| (env, vars) -> begin
(

let uu____4650 = (gen_term_var env v)
in (match (uu____4650) with
| (xx, uu____4662, env) -> begin
((env), ((((v), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars))
end))
end)) ((env), ([]))))
in (match (uu____4599) with
| (env, vars) -> begin
(

let rec mk_guard = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4709) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_dot_term (_)) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____4717 = (

let uu____4720 = (encode_const c)
in ((scrutinee), (uu____4720)))
in (FStar_SMTEncoding_Util.mkEq uu____4717))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (

let tc_name = (FStar_TypeChecker_Env.typ_of_datacon env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____4739 = (FStar_TypeChecker_Env.datacons_of_typ env.tcenv tc_name)
in (match (uu____4739) with
| (uu____4743, (uu____4744)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____4746 -> begin
(mk_data_tester env f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
end)))
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4767 -> (match (uu____4767) with
| (arg, uu____4773) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____4783 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____4783)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat scrutinee -> (match (pat.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_disj (uu____4802) -> begin
(failwith "Impossible")
end
| (FStar_Syntax_Syntax.Pat_dot_term (x, _)) | (FStar_Syntax_Syntax.Pat_var (x)) | (FStar_Syntax_Syntax.Pat_wild (x)) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____4817) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____4832 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____4854 -> (match (uu____4854) with
| (arg, uu____4863) -> begin
(

let proj = (primitive_projector_by_pos env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____4873 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____4873)))
end))))
in (FStar_All.pipe_right uu____4832 FStar_List.flatten))
end))
in (

let pat_term = (fun uu____4889 -> (encode_term pat_term env))
in (

let pattern = {pat_vars = vars; pat_term = pat_term; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____4896 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____4911 uu____4912 -> (match (((uu____4911), (uu____4912))) with
| ((tms, decls), (t, uu____4932)) -> begin
(

let uu____4943 = (encode_term t env)
in (match (uu____4943) with
| (t, decls') -> begin
(((t)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____4896) with
| (l, decls) -> begin
(((FStar_List.rev l)), (decls))
end)))
and encode_function_type_as_formula : FStar_SMTEncoding_Term.term Prims.option  ->  FStar_Syntax_Syntax.term Prims.option  ->  FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun induction_on new_pats t env -> (

let list_elements = (fun e -> (

let uu____4981 = (FStar_Syntax_Util.list_elements e)
in (match (uu____4981) with
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

let uu____4999 = (

let uu____5009 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____5009 FStar_Syntax_Util.head_and_args))
in (match (uu____4999) with
| (head, args) -> begin
(

let uu____5040 = (

let uu____5048 = (

let uu____5049 = (FStar_Syntax_Util.un_uinst head)
in uu____5049.FStar_Syntax_Syntax.n)
in ((uu____5048), (args)))
in (match (uu____5040) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____5063, uu____5064))::((e, uu____5066))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpat_lid) -> begin
((e), (None))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5097))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatT_lid) -> begin
((e), (None))
end
| uu____5118 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements p)
in (

let smt_pat_or = (fun t -> (

let uu____5151 = (

let uu____5161 = (FStar_Syntax_Util.unmeta t)
in (FStar_All.pipe_right uu____5161 FStar_Syntax_Util.head_and_args))
in (match (uu____5151) with
| (head, args) -> begin
(

let uu____5190 = (

let uu____5198 = (

let uu____5199 = (FStar_Syntax_Util.un_uinst head)
in uu____5199.FStar_Syntax_Syntax.n)
in ((uu____5198), (args)))
in (match (uu____5190) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____5212))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.smtpatOr_lid) -> begin
Some (e)
end
| uu____5232 -> begin
None
end))
end)))
in (match (elts) with
| (t)::[] -> begin
(

let uu____5250 = (smt_pat_or t)
in (match (uu____5250) with
| Some (e) -> begin
(

let uu____5266 = (list_elements e)
in (FStar_All.pipe_right uu____5266 (FStar_List.map (fun branch -> (

let uu____5283 = (list_elements branch)
in (FStar_All.pipe_right uu____5283 (FStar_List.map one_pat)))))))
end
| uu____5297 -> begin
(

let uu____5301 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5301)::[])
end))
end
| uu____5332 -> begin
(

let uu____5334 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____5334)::[])
end))))
in (

let uu____5365 = (

let uu____5381 = (

let uu____5382 = (FStar_Syntax_Subst.compress t)
in uu____5382.FStar_Syntax_Syntax.n)
in (match (uu____5381) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____5412 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____5412) with
| (binders, c) -> begin
(match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____5447; FStar_Syntax_Syntax.effect_name = uu____5448; FStar_Syntax_Syntax.result_typ = uu____5449; FStar_Syntax_Syntax.effect_args = ((pre, uu____5451))::((post, uu____5453))::((pats, uu____5455))::[]; FStar_Syntax_Syntax.flags = uu____5456}) -> begin
(

let pats' = (match (new_pats) with
| Some (new_pats') -> begin
new_pats'
end
| None -> begin
pats
end)
in (

let uu____5490 = (lemma_pats pats')
in ((binders), (pre), (post), (uu____5490))))
end
| uu____5509 -> begin
(failwith "impos")
end)
end))
end
| uu____5525 -> begin
(failwith "Impos")
end))
in (match (uu____5365) with
| (binders, pre, post, patterns) -> begin
(

let uu____5569 = (encode_binders None binders env)
in (match (uu____5569) with
| (vars, guards, env, decls, uu____5584) -> begin
(

let uu____5591 = (

let uu____5598 = (FStar_All.pipe_right patterns (FStar_List.map (fun branch -> (

let uu____5629 = (

let uu____5634 = (FStar_All.pipe_right branch (FStar_List.map (fun uu____5650 -> (match (uu____5650) with
| (t, uu____5657) -> begin
(encode_term t (

let uu___144_5660 = env
in {bindings = uu___144_5660.bindings; depth = uu___144_5660.depth; tcenv = uu___144_5660.tcenv; warn = uu___144_5660.warn; cache = uu___144_5660.cache; nolabels = uu___144_5660.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___144_5660.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right uu____5634 FStar_List.unzip))
in (match (uu____5629) with
| (pats, decls) -> begin
((pats), (decls))
end)))))
in (FStar_All.pipe_right uu____5598 FStar_List.unzip))
in (match (uu____5591) with
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

let uu____5724 = (

let uu____5725 = (FStar_SMTEncoding_Util.mkFreeV l)
in (FStar_SMTEncoding_Util.mk_Precedes uu____5725 e))
in (uu____5724)::p))))
end
| uu____5726 -> begin
(

let rec aux = (fun tl vars -> (match (vars) with
| [] -> begin
(FStar_All.pipe_right pats (FStar_List.map (fun p -> (

let uu____5755 = (FStar_SMTEncoding_Util.mk_Precedes tl e)
in (uu____5755)::p))))
end
| ((x, FStar_SMTEncoding_Term.Term_sort))::vars -> begin
(

let uu____5763 = (

let uu____5764 = (FStar_SMTEncoding_Util.mkFreeV ((x), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_SMTEncoding_Util.mk_LexCons uu____5764 tl))
in (aux uu____5763 vars))
end
| uu____5765 -> begin
pats
end))
in (

let uu____5769 = (FStar_SMTEncoding_Util.mkFreeV (("Prims.LexTop"), (FStar_SMTEncoding_Term.Term_sort)))
in (aux uu____5769 vars)))
end)
end)
in (

let env = (

let uu___145_5771 = env
in {bindings = uu___145_5771.bindings; depth = uu___145_5771.depth; tcenv = uu___145_5771.tcenv; warn = uu___145_5771.warn; cache = uu___145_5771.cache; nolabels = true; use_zfuel_name = uu___145_5771.use_zfuel_name; encode_non_total_function_typ = uu___145_5771.encode_non_total_function_typ})
in (

let uu____5772 = (

let uu____5775 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____5775 env))
in (match (uu____5772) with
| (pre, decls'') -> begin
(

let uu____5780 = (

let uu____5783 = (FStar_Syntax_Util.unmeta post)
in (encode_formula uu____5783 env))
in (match (uu____5780) with
| (post, decls''') -> begin
(

let decls = (FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') (FStar_List.append decls'' decls''')))
in (

let uu____5790 = (

let uu____5791 = (

let uu____5797 = (

let uu____5798 = (

let uu____5801 = (FStar_SMTEncoding_Util.mk_and_l ((pre)::guards))
in ((uu____5801), (post)))
in (FStar_SMTEncoding_Util.mkImp uu____5798))
in ((pats), (vars), (uu____5797)))
in (FStar_SMTEncoding_Util.mkForall uu____5791))
in ((uu____5790), (decls))))
end))
end)))))
end))
end))
end))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug = (fun phi -> (

let uu____5814 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____5814) with
| true -> begin
(

let uu____5815 = (FStar_Syntax_Print.tag_of_term phi)
in (

let uu____5816 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____5815 uu____5816)))
end
| uu____5817 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____5843 = (FStar_Util.fold_map (fun decls x -> (

let uu____5856 = (encode_term (Prims.fst x) env)
in (match (uu____5856) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____5843) with
| (decls, args) -> begin
(

let uu____5873 = (

let uu___146_5874 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___146_5874.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___146_5874.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____5873), (decls)))
end)))
in (

let const_op = (fun f r uu____5893 -> (

let uu____5896 = (f r)
in ((uu____5896), ([]))))
in (

let un_op = (fun f l -> (

let uu____5912 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____5912)))
in (

let bin_op = (fun f uu___119_5925 -> (match (uu___119_5925) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____5933 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____5960 = (FStar_Util.fold_map (fun decls uu____5969 -> (match (uu____5969) with
| (t, uu____5977) -> begin
(

let uu____5978 = (encode_formula t env)
in (match (uu____5978) with
| (phi, decls') -> begin
(((FStar_List.append decls decls')), (phi))
end))
end)) [] l)
in (match (uu____5960) with
| (decls, phis) -> begin
(

let uu____5995 = (

let uu___147_5996 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___147_5996.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___147_5996.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____5995), (decls)))
end)))
in (

let eq_op = (fun r uu___120_6012 -> (match (uu___120_6012) with
| ((_)::(e1)::(e2)::[]) | ((_)::(_)::(e1)::(e2)::[]) -> begin
(

let uu____6072 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____6072 r ((e1)::(e2)::[])))
end
| l -> begin
(

let uu____6092 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____6092 r l))
end))
in (

let mk_imp = (fun r uu___121_6111 -> (match (uu___121_6111) with
| ((lhs, uu____6115))::((rhs, uu____6117))::[] -> begin
(

let uu____6138 = (encode_formula rhs env)
in (match (uu____6138) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____6147) -> begin
((l1), (decls1))
end
| uu____6150 -> begin
(

let uu____6151 = (encode_formula lhs env)
in (match (uu____6151) with
| (l2, decls2) -> begin
(

let uu____6158 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____6158), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____6160 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___122_6175 -> (match (uu___122_6175) with
| ((guard, uu____6179))::((_then, uu____6181))::((_else, uu____6183))::[] -> begin
(

let uu____6212 = (encode_formula guard env)
in (match (uu____6212) with
| (g, decls1) -> begin
(

let uu____6219 = (encode_formula _then env)
in (match (uu____6219) with
| (t, decls2) -> begin
(

let uu____6226 = (encode_formula _else env)
in (match (uu____6226) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____6235 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____6254 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____6254)))
in (

let connectives = (

let uu____6266 = (

let uu____6275 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Syntax_Const.and_lid), (uu____6275)))
in (

let uu____6288 = (

let uu____6298 = (

let uu____6307 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Syntax_Const.or_lid), (uu____6307)))
in (

let uu____6320 = (

let uu____6330 = (

let uu____6340 = (

let uu____6349 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Syntax_Const.iff_lid), (uu____6349)))
in (

let uu____6362 = (

let uu____6372 = (

let uu____6382 = (

let uu____6391 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Syntax_Const.not_lid), (uu____6391)))
in (uu____6382)::(((FStar_Syntax_Const.eq2_lid), (eq_op)))::(((FStar_Syntax_Const.eq3_lid), (eq_op)))::(((FStar_Syntax_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Syntax_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Syntax_Const.ite_lid), (mk_ite)))::uu____6372)
in (uu____6340)::uu____6362))
in (((FStar_Syntax_Const.imp_lid), (mk_imp)))::uu____6330)
in (uu____6298)::uu____6320))
in (uu____6266)::uu____6288))
in (

let rec fallback = (fun phi -> (match (phi.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____6553 = (encode_formula phi' env)
in (match (uu____6553) with
| (phi, decls) -> begin
(

let uu____6560 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi), (msg), (r)))) r)
in ((uu____6560), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____6561) -> begin
(

let uu____6566 = (FStar_Syntax_Util.unmeta phi)
in (encode_formula uu____6566 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____6595 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____6595) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____6603; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____6605; FStar_Syntax_Syntax.lbdef = e1})::[]), e2) -> begin
(

let uu____6621 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____6621) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head, args) -> begin
(

let head = (FStar_Syntax_Util.un_uinst head)
in (match (((head.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____6653)::((x, uu____6655))::((t, uu____6657))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.has_type_lid) -> begin
(

let uu____6691 = (encode_term x env)
in (match (uu____6691) with
| (x, decls) -> begin
(

let uu____6698 = (encode_term t env)
in (match (uu____6698) with
| (t, decls') -> begin
(

let uu____6705 = (FStar_SMTEncoding_Term.mk_HasType x t)
in ((uu____6705), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____6709))::((msg, uu____6711))::((phi, uu____6713))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.labeled_lid) -> begin
(

let uu____6747 = (

let uu____6750 = (

let uu____6751 = (FStar_Syntax_Subst.compress r)
in uu____6751.FStar_Syntax_Syntax.n)
in (

let uu____6754 = (

let uu____6755 = (FStar_Syntax_Subst.compress msg)
in uu____6755.FStar_Syntax_Syntax.n)
in ((uu____6750), (uu____6754))))
in (match (uu____6747) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____6762))) -> begin
(

let phi = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi), (FStar_Syntax_Syntax.Meta_labeled ((((FStar_Util.string_of_unicode s)), (r), (false)))))))) None r)
in (fallback phi))
end
| uu____6778 -> begin
(fallback phi)
end))
end
| uu____6781 when (head_redex env head) -> begin
(

let uu____6789 = (whnf env phi)
in (encode_formula uu____6789 env))
end
| uu____6790 -> begin
(

let uu____6798 = (encode_term phi env)
in (match (uu____6798) with
| (tt, decls) -> begin
(

let uu____6805 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___148_6806 = tt
in {FStar_SMTEncoding_Term.tm = uu___148_6806.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___148_6806.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((uu____6805), (decls)))
end))
end))
end
| uu____6809 -> begin
(

let uu____6810 = (encode_term phi env)
in (match (uu____6810) with
| (tt, decls) -> begin
(

let uu____6817 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___149_6818 = tt
in {FStar_SMTEncoding_Term.tm = uu___149_6818.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___149_6818.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi.FStar_Syntax_Syntax.pos}))
in ((uu____6817), (decls)))
end))
end))
in (

let encode_q_body = (fun env bs ps body -> (

let uu____6845 = (encode_binders None bs env)
in (match (uu____6845) with
| (vars, guards, env, decls, uu____6867) -> begin
(

let uu____6874 = (

let uu____6881 = (FStar_All.pipe_right ps (FStar_List.map (fun p -> (

let uu____6904 = (

let uu____6909 = (FStar_All.pipe_right p (FStar_List.map (fun uu____6923 -> (match (uu____6923) with
| (t, uu____6929) -> begin
(encode_term t (

let uu___150_6930 = env
in {bindings = uu___150_6930.bindings; depth = uu___150_6930.depth; tcenv = uu___150_6930.tcenv; warn = uu___150_6930.warn; cache = uu___150_6930.cache; nolabels = uu___150_6930.nolabels; use_zfuel_name = true; encode_non_total_function_typ = uu___150_6930.encode_non_total_function_typ}))
end))))
in (FStar_All.pipe_right uu____6909 FStar_List.unzip))
in (match (uu____6904) with
| (p, decls) -> begin
((p), ((FStar_List.flatten decls)))
end)))))
in (FStar_All.pipe_right uu____6881 FStar_List.unzip))
in (match (uu____6874) with
| (pats, decls') -> begin
(

let uu____6982 = (encode_formula body env)
in (match (uu____6982) with
| (body, decls'') -> begin
(

let guards = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____7001; FStar_SMTEncoding_Term.rng = uu____7002})::[])::[] when ((FStar_Ident.text_of_lid FStar_Syntax_Const.guard_free) = gf) -> begin
[]
end
| uu____7010 -> begin
guards
end)
in (

let uu____7013 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((vars), (pats), (uu____7013), (body), ((FStar_List.append decls (FStar_List.append (FStar_List.flatten decls') decls''))))))
end))
end))
end)))
in ((debug phi);
(

let phi = (FStar_Syntax_Util.unascribe phi)
in (

let check_pattern_vars = (fun vars pats -> (

let pats = (FStar_All.pipe_right pats (FStar_List.map (fun uu____7047 -> (match (uu____7047) with
| (x, uu____7051) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x)
end))))
in (match (pats) with
| [] -> begin
()
end
| (hd)::tl -> begin
(

let pat_vars = (

let uu____7057 = (FStar_Syntax_Free.names hd)
in (FStar_List.fold_left (fun out x -> (

let uu____7063 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____7063))) uu____7057 tl))
in (

let uu____7065 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____7077 -> (match (uu____7077) with
| (b, uu____7081) -> begin
(

let uu____7082 = (FStar_Util.set_mem b pat_vars)
in (not (uu____7082)))
end))))
in (match (uu____7065) with
| None -> begin
()
end
| Some (x, uu____7086) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd.FStar_Syntax_Syntax.pos tl)
in (

let uu____7096 = (

let uu____7097 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____7097))
in (FStar_Errors.warn pos uu____7096)))
end)))
end)))
in (

let uu____7098 = (FStar_Syntax_Util.destruct_typ_as_formula phi)
in (match (uu____7098) with
| None -> begin
(fallback phi)
end
| Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____7104 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____7140 -> (match (uu____7140) with
| (l, uu____7150) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____7104) with
| None -> begin
(fallback phi)
end
| Some (uu____7173, f) -> begin
(f phi.FStar_Syntax_Syntax.pos arms)
end))
end
| Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7202 = (encode_q_body env vars pats body)
in (match (uu____7202) with
| (vars, pats, guard, body, decls) -> begin
(

let tm = (

let uu____7228 = (

let uu____7234 = (FStar_SMTEncoding_Util.mkImp ((guard), (body)))
in ((pats), (vars), (uu____7234)))
in (FStar_SMTEncoding_Term.mkForall uu____7228 phi.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars vars)));
(

let uu____7246 = (encode_q_body env vars pats body)
in (match (uu____7246) with
| (vars, pats, guard, body, decls) -> begin
(

let uu____7271 = (

let uu____7272 = (

let uu____7278 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body)))
in ((pats), (vars), (uu____7278)))
in (FStar_SMTEncoding_Term.mkExists uu____7272 phi.FStar_Syntax_Syntax.pos))
in ((uu____7271), (decls)))
end));
)
end))));
)))))))))))))))

type prims_t =
{mk : FStar_Ident.lident  ->  Prims.string  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list); is : FStar_Ident.lident  ->  Prims.bool}


let prims : prims_t = (

let uu____7327 = (fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7327) with
| (asym, a) -> begin
(

let uu____7332 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7332) with
| (xsym, x) -> begin
(

let uu____7337 = (fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____7337) with
| (ysym, y) -> begin
(

let quant = (fun vars body x -> (

let xname_decl = (

let uu____7367 = (

let uu____7373 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in ((x), (uu____7373), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____7367))
in (

let xtok = (Prims.strcat x "@tok")
in (

let xtok_decl = FStar_SMTEncoding_Term.DeclFun (((xtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let xapp = (

let uu____7388 = (

let uu____7392 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((x), (uu____7392)))
in (FStar_SMTEncoding_Util.mkApp uu____7388))
in (

let xtok = (FStar_SMTEncoding_Util.mkApp ((xtok), ([])))
in (

let xtok_app = (mk_Apply xtok vars)
in (

let uu____7400 = (

let uu____7402 = (

let uu____7404 = (

let uu____7406 = (

let uu____7407 = (

let uu____7412 = (

let uu____7413 = (

let uu____7419 = (FStar_SMTEncoding_Util.mkEq ((xapp), (body)))
in ((((xapp)::[])::[]), (vars), (uu____7419)))
in (FStar_SMTEncoding_Util.mkForall uu____7413))
in ((uu____7412), (None), (Some ((Prims.strcat "primitive_" x)))))
in FStar_SMTEncoding_Term.Assume (uu____7407))
in (

let uu____7429 = (

let uu____7431 = (

let uu____7432 = (

let uu____7437 = (

let uu____7438 = (

let uu____7444 = (FStar_SMTEncoding_Util.mkEq ((xtok_app), (xapp)))
in ((((xtok_app)::[])::[]), (vars), (uu____7444)))
in (FStar_SMTEncoding_Util.mkForall uu____7438))
in ((uu____7437), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" x)))))
in FStar_SMTEncoding_Term.Assume (uu____7432))
in (uu____7431)::[])
in (uu____7406)::uu____7429))
in (xtok_decl)::uu____7404)
in (xname_decl)::uu____7402)
in ((xtok), (uu____7400))))))))))
in (

let axy = (((asym), (FStar_SMTEncoding_Term.Term_sort)))::(((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let xy = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ysym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let qx = (((xsym), (FStar_SMTEncoding_Term.Term_sort)))::[]
in (

let prims = (

let uu____7494 = (

let uu____7502 = (

let uu____7508 = (

let uu____7509 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7509))
in (quant axy uu____7508))
in ((FStar_Syntax_Const.op_Eq), (uu____7502)))
in (

let uu____7515 = (

let uu____7524 = (

let uu____7532 = (

let uu____7538 = (

let uu____7539 = (

let uu____7540 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in (FStar_SMTEncoding_Util.mkNot uu____7540))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7539))
in (quant axy uu____7538))
in ((FStar_Syntax_Const.op_notEq), (uu____7532)))
in (

let uu____7546 = (

let uu____7555 = (

let uu____7563 = (

let uu____7569 = (

let uu____7570 = (

let uu____7571 = (

let uu____7574 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7575 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7574), (uu____7575))))
in (FStar_SMTEncoding_Util.mkLT uu____7571))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7570))
in (quant xy uu____7569))
in ((FStar_Syntax_Const.op_LT), (uu____7563)))
in (

let uu____7581 = (

let uu____7590 = (

let uu____7598 = (

let uu____7604 = (

let uu____7605 = (

let uu____7606 = (

let uu____7609 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7610 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7609), (uu____7610))))
in (FStar_SMTEncoding_Util.mkLTE uu____7606))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7605))
in (quant xy uu____7604))
in ((FStar_Syntax_Const.op_LTE), (uu____7598)))
in (

let uu____7616 = (

let uu____7625 = (

let uu____7633 = (

let uu____7639 = (

let uu____7640 = (

let uu____7641 = (

let uu____7644 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7645 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7644), (uu____7645))))
in (FStar_SMTEncoding_Util.mkGT uu____7641))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7640))
in (quant xy uu____7639))
in ((FStar_Syntax_Const.op_GT), (uu____7633)))
in (

let uu____7651 = (

let uu____7660 = (

let uu____7668 = (

let uu____7674 = (

let uu____7675 = (

let uu____7676 = (

let uu____7679 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7680 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7679), (uu____7680))))
in (FStar_SMTEncoding_Util.mkGTE uu____7676))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7675))
in (quant xy uu____7674))
in ((FStar_Syntax_Const.op_GTE), (uu____7668)))
in (

let uu____7686 = (

let uu____7695 = (

let uu____7703 = (

let uu____7709 = (

let uu____7710 = (

let uu____7711 = (

let uu____7714 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7715 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7714), (uu____7715))))
in (FStar_SMTEncoding_Util.mkSub uu____7711))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7710))
in (quant xy uu____7709))
in ((FStar_Syntax_Const.op_Subtraction), (uu____7703)))
in (

let uu____7721 = (

let uu____7730 = (

let uu____7738 = (

let uu____7744 = (

let uu____7745 = (

let uu____7746 = (FStar_SMTEncoding_Term.unboxInt x)
in (FStar_SMTEncoding_Util.mkMinus uu____7746))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7745))
in (quant qx uu____7744))
in ((FStar_Syntax_Const.op_Minus), (uu____7738)))
in (

let uu____7752 = (

let uu____7761 = (

let uu____7769 = (

let uu____7775 = (

let uu____7776 = (

let uu____7777 = (

let uu____7780 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7781 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7780), (uu____7781))))
in (FStar_SMTEncoding_Util.mkAdd uu____7777))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7776))
in (quant xy uu____7775))
in ((FStar_Syntax_Const.op_Addition), (uu____7769)))
in (

let uu____7787 = (

let uu____7796 = (

let uu____7804 = (

let uu____7810 = (

let uu____7811 = (

let uu____7812 = (

let uu____7815 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7816 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7815), (uu____7816))))
in (FStar_SMTEncoding_Util.mkMul uu____7812))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7811))
in (quant xy uu____7810))
in ((FStar_Syntax_Const.op_Multiply), (uu____7804)))
in (

let uu____7822 = (

let uu____7831 = (

let uu____7839 = (

let uu____7845 = (

let uu____7846 = (

let uu____7847 = (

let uu____7850 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7851 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7850), (uu____7851))))
in (FStar_SMTEncoding_Util.mkDiv uu____7847))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7846))
in (quant xy uu____7845))
in ((FStar_Syntax_Const.op_Division), (uu____7839)))
in (

let uu____7857 = (

let uu____7866 = (

let uu____7874 = (

let uu____7880 = (

let uu____7881 = (

let uu____7882 = (

let uu____7885 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____7886 = (FStar_SMTEncoding_Term.unboxInt y)
in ((uu____7885), (uu____7886))))
in (FStar_SMTEncoding_Util.mkMod uu____7882))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxInt uu____7881))
in (quant xy uu____7880))
in ((FStar_Syntax_Const.op_Modulus), (uu____7874)))
in (

let uu____7892 = (

let uu____7901 = (

let uu____7909 = (

let uu____7915 = (

let uu____7916 = (

let uu____7917 = (

let uu____7920 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____7921 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____7920), (uu____7921))))
in (FStar_SMTEncoding_Util.mkAnd uu____7917))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7916))
in (quant xy uu____7915))
in ((FStar_Syntax_Const.op_And), (uu____7909)))
in (

let uu____7927 = (

let uu____7936 = (

let uu____7944 = (

let uu____7950 = (

let uu____7951 = (

let uu____7952 = (

let uu____7955 = (FStar_SMTEncoding_Term.unboxBool x)
in (

let uu____7956 = (FStar_SMTEncoding_Term.unboxBool y)
in ((uu____7955), (uu____7956))))
in (FStar_SMTEncoding_Util.mkOr uu____7952))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7951))
in (quant xy uu____7950))
in ((FStar_Syntax_Const.op_Or), (uu____7944)))
in (

let uu____7962 = (

let uu____7971 = (

let uu____7979 = (

let uu____7985 = (

let uu____7986 = (

let uu____7987 = (FStar_SMTEncoding_Term.unboxBool x)
in (FStar_SMTEncoding_Util.mkNot uu____7987))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____7986))
in (quant qx uu____7985))
in ((FStar_Syntax_Const.op_Negation), (uu____7979)))
in (uu____7971)::[])
in (uu____7936)::uu____7962))
in (uu____7901)::uu____7927))
in (uu____7866)::uu____7892))
in (uu____7831)::uu____7857))
in (uu____7796)::uu____7822))
in (uu____7761)::uu____7787))
in (uu____7730)::uu____7752))
in (uu____7695)::uu____7721))
in (uu____7660)::uu____7686))
in (uu____7625)::uu____7651))
in (uu____7590)::uu____7616))
in (uu____7555)::uu____7581))
in (uu____7524)::uu____7546))
in (uu____7494)::uu____7515))
in (

let mk = (fun l v -> (

let uu____8115 = (

let uu____8120 = (FStar_All.pipe_right prims (FStar_List.find (fun uu____8152 -> (match (uu____8152) with
| (l', uu____8161) -> begin
(FStar_Ident.lid_equals l l')
end))))
in (FStar_All.pipe_right uu____8120 (FStar_Option.map (fun uu____8194 -> (match (uu____8194) with
| (uu____8205, b) -> begin
(b v)
end)))))
in (FStar_All.pipe_right uu____8115 FStar_Option.get)))
in (

let is = (fun l -> (FStar_All.pipe_right prims (FStar_Util.for_some (fun uu____8246 -> (match (uu____8246) with
| (l', uu____8255) -> begin
(FStar_Ident.lid_equals l l')
end)))))
in {mk = mk; is = is})))))))
end))
end))
end))


let pretype_axiom : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.decl = (fun tapp vars -> (

let uu____8278 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____8278) with
| (xxsym, xx) -> begin
(

let uu____8283 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____8283) with
| (ffsym, ff) -> begin
(

let xx_has_type = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let tapp_hash = (FStar_SMTEncoding_Term.hash_of_term tapp)
in (

let uu____8290 = (

let uu____8295 = (

let uu____8296 = (

let uu____8302 = (

let uu____8303 = (

let uu____8306 = (

let uu____8307 = (

let uu____8310 = (FStar_SMTEncoding_Util.mkApp (("PreType"), ((xx)::[])))
in ((tapp), (uu____8310)))
in (FStar_SMTEncoding_Util.mkEq uu____8307))
in ((xx_has_type), (uu____8306)))
in (FStar_SMTEncoding_Util.mkImp uu____8303))
in ((((xx_has_type)::[])::[]), ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::(((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars), (uu____8302)))
in (FStar_SMTEncoding_Util.mkForall uu____8296))
in (

let uu____8323 = (

let uu____8325 = (

let uu____8326 = (

let uu____8327 = (FStar_Util.digest_of_string tapp_hash)
in (Prims.strcat "pretyping_" uu____8327))
in (varops.mk_unique uu____8326))
in Some (uu____8325))
in ((uu____8295), (Some ("pretyping")), (uu____8323))))
in FStar_SMTEncoding_Term.Assume (uu____8290))))
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

let uu____8358 = (

let uu____8359 = (

let uu____8364 = (FStar_SMTEncoding_Term.mk_HasType FStar_SMTEncoding_Term.mk_Term_unit tt)
in ((uu____8364), (Some ("unit typing")), (Some ("unit_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8359))
in (

let uu____8367 = (

let uu____8369 = (

let uu____8370 = (

let uu____8375 = (

let uu____8376 = (

let uu____8382 = (

let uu____8383 = (

let uu____8386 = (FStar_SMTEncoding_Util.mkEq ((x), (FStar_SMTEncoding_Term.mk_Term_unit)))
in ((typing_pred), (uu____8386)))
in (FStar_SMTEncoding_Util.mkImp uu____8383))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8382)))
in (mkForall_fuel uu____8376))
in ((uu____8375), (Some ("unit inversion")), (Some ("unit_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8370))
in (uu____8369)::[])
in (uu____8358)::uu____8367))))
in (

let mk_bool = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Bool_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8415 = (

let uu____8416 = (

let uu____8421 = (

let uu____8422 = (

let uu____8428 = (

let uu____8431 = (

let uu____8433 = (FStar_SMTEncoding_Term.boxBool b)
in (uu____8433)::[])
in (uu____8431)::[])
in (

let uu____8436 = (

let uu____8437 = (FStar_SMTEncoding_Term.boxBool b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8437 tt))
in ((uu____8428), ((bb)::[]), (uu____8436))))
in (FStar_SMTEncoding_Util.mkForall uu____8422))
in ((uu____8421), (Some ("bool typing")), (Some ("bool_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8416))
in (

let uu____8449 = (

let uu____8451 = (

let uu____8452 = (

let uu____8457 = (

let uu____8458 = (

let uu____8464 = (

let uu____8465 = (

let uu____8468 = (FStar_SMTEncoding_Term.mk_tester "BoxBool" x)
in ((typing_pred), (uu____8468)))
in (FStar_SMTEncoding_Util.mkImp uu____8465))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8464)))
in (mkForall_fuel uu____8458))
in ((uu____8457), (Some ("bool inversion")), (Some ("bool_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8452))
in (uu____8451)::[])
in (uu____8415)::uu____8449))))))
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

let uu____8503 = (

let uu____8504 = (

let uu____8508 = (

let uu____8510 = (

let uu____8512 = (

let uu____8514 = (FStar_SMTEncoding_Term.boxInt a)
in (

let uu____8515 = (

let uu____8517 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8517)::[])
in (uu____8514)::uu____8515))
in (tt)::uu____8512)
in (tt)::uu____8510)
in (("Prims.Precedes"), (uu____8508)))
in (FStar_SMTEncoding_Util.mkApp uu____8504))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8503))
in (

let precedes_y_x = (

let uu____8520 = (FStar_SMTEncoding_Util.mkApp (("Precedes"), ((y)::(x)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8520))
in (

let uu____8522 = (

let uu____8523 = (

let uu____8528 = (

let uu____8529 = (

let uu____8535 = (

let uu____8538 = (

let uu____8540 = (FStar_SMTEncoding_Term.boxInt b)
in (uu____8540)::[])
in (uu____8538)::[])
in (

let uu____8543 = (

let uu____8544 = (FStar_SMTEncoding_Term.boxInt b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8544 tt))
in ((uu____8535), ((bb)::[]), (uu____8543))))
in (FStar_SMTEncoding_Util.mkForall uu____8529))
in ((uu____8528), (Some ("int typing")), (Some ("int_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8523))
in (

let uu____8556 = (

let uu____8558 = (

let uu____8559 = (

let uu____8564 = (

let uu____8565 = (

let uu____8571 = (

let uu____8572 = (

let uu____8575 = (FStar_SMTEncoding_Term.mk_tester "BoxInt" x)
in ((typing_pred), (uu____8575)))
in (FStar_SMTEncoding_Util.mkImp uu____8572))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8571)))
in (mkForall_fuel uu____8565))
in ((uu____8564), (Some ("int inversion")), (Some ("int_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8559))
in (

let uu____8589 = (

let uu____8591 = (

let uu____8592 = (

let uu____8597 = (

let uu____8598 = (

let uu____8604 = (

let uu____8605 = (

let uu____8608 = (

let uu____8609 = (

let uu____8611 = (

let uu____8613 = (

let uu____8615 = (

let uu____8616 = (

let uu____8619 = (FStar_SMTEncoding_Term.unboxInt x)
in (

let uu____8620 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8619), (uu____8620))))
in (FStar_SMTEncoding_Util.mkGT uu____8616))
in (

let uu____8621 = (

let uu____8623 = (

let uu____8624 = (

let uu____8627 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8628 = (FStar_SMTEncoding_Util.mkInteger' (Prims.parse_int "0"))
in ((uu____8627), (uu____8628))))
in (FStar_SMTEncoding_Util.mkGTE uu____8624))
in (

let uu____8629 = (

let uu____8631 = (

let uu____8632 = (

let uu____8635 = (FStar_SMTEncoding_Term.unboxInt y)
in (

let uu____8636 = (FStar_SMTEncoding_Term.unboxInt x)
in ((uu____8635), (uu____8636))))
in (FStar_SMTEncoding_Util.mkLT uu____8632))
in (uu____8631)::[])
in (uu____8623)::uu____8629))
in (uu____8615)::uu____8621))
in (typing_pred_y)::uu____8613)
in (typing_pred)::uu____8611)
in (FStar_SMTEncoding_Util.mk_and_l uu____8609))
in ((uu____8608), (precedes_y_x)))
in (FStar_SMTEncoding_Util.mkImp uu____8605))
in ((((typing_pred)::(typing_pred_y)::(precedes_y_x)::[])::[]), ((xx)::(yy)::[]), (uu____8604)))
in (mkForall_fuel uu____8598))
in ((uu____8597), (Some ("well-founded ordering on nat (alt)")), (Some ("well-founded-ordering-on-nat"))))
in FStar_SMTEncoding_Term.Assume (uu____8592))
in (uu____8591)::[])
in (uu____8558)::uu____8589))
in (uu____8522)::uu____8556)))))))))))
in (

let mk_str = (fun env nm tt -> (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x tt)
in (

let bb = (("b"), (FStar_SMTEncoding_Term.String_sort))
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let uu____8667 = (

let uu____8668 = (

let uu____8673 = (

let uu____8674 = (

let uu____8680 = (

let uu____8683 = (

let uu____8685 = (FStar_SMTEncoding_Term.boxString b)
in (uu____8685)::[])
in (uu____8683)::[])
in (

let uu____8688 = (

let uu____8689 = (FStar_SMTEncoding_Term.boxString b)
in (FStar_SMTEncoding_Term.mk_HasType uu____8689 tt))
in ((uu____8680), ((bb)::[]), (uu____8688))))
in (FStar_SMTEncoding_Util.mkForall uu____8674))
in ((uu____8673), (Some ("string typing")), (Some ("string_typing"))))
in FStar_SMTEncoding_Term.Assume (uu____8668))
in (

let uu____8701 = (

let uu____8703 = (

let uu____8704 = (

let uu____8709 = (

let uu____8710 = (

let uu____8716 = (

let uu____8717 = (

let uu____8720 = (FStar_SMTEncoding_Term.mk_tester "BoxString" x)
in ((typing_pred), (uu____8720)))
in (FStar_SMTEncoding_Util.mkImp uu____8717))
in ((((typing_pred)::[])::[]), ((xx)::[]), (uu____8716)))
in (mkForall_fuel uu____8710))
in ((uu____8709), (Some ("string inversion")), (Some ("string_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8704))
in (uu____8703)::[])
in (uu____8667)::uu____8701))))))
in (

let mk_ref = (fun env reft_name uu____8743 -> (

let r = (("r"), (FStar_SMTEncoding_Term.Ref_sort))
in (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let refa = (

let uu____8754 = (

let uu____8758 = (

let uu____8760 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (uu____8760)::[])
in ((reft_name), (uu____8758)))
in (FStar_SMTEncoding_Util.mkApp uu____8754))
in (

let refb = (

let uu____8763 = (

let uu____8767 = (

let uu____8769 = (FStar_SMTEncoding_Util.mkFreeV bb)
in (uu____8769)::[])
in ((reft_name), (uu____8767)))
in (FStar_SMTEncoding_Util.mkApp uu____8763))
in (

let typing_pred = (FStar_SMTEncoding_Term.mk_HasType x refa)
in (

let typing_pred_b = (FStar_SMTEncoding_Term.mk_HasType x refb)
in (

let uu____8773 = (

let uu____8774 = (

let uu____8779 = (

let uu____8780 = (

let uu____8786 = (

let uu____8787 = (

let uu____8790 = (FStar_SMTEncoding_Term.mk_tester "BoxRef" x)
in ((typing_pred), (uu____8790)))
in (FStar_SMTEncoding_Util.mkImp uu____8787))
in ((((typing_pred)::[])::[]), ((xx)::(aa)::[]), (uu____8786)))
in (mkForall_fuel uu____8780))
in ((uu____8779), (Some ("ref inversion")), (Some ("ref_inversion"))))
in FStar_SMTEncoding_Term.Assume (uu____8774))
in (

let uu____8806 = (

let uu____8808 = (

let uu____8809 = (

let uu____8814 = (

let uu____8815 = (

let uu____8821 = (

let uu____8822 = (

let uu____8825 = (FStar_SMTEncoding_Util.mkAnd ((typing_pred), (typing_pred_b)))
in (

let uu____8826 = (

let uu____8827 = (

let uu____8830 = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let uu____8831 = (FStar_SMTEncoding_Util.mkFreeV bb)
in ((uu____8830), (uu____8831))))
in (FStar_SMTEncoding_Util.mkEq uu____8827))
in ((uu____8825), (uu____8826))))
in (FStar_SMTEncoding_Util.mkImp uu____8822))
in ((((typing_pred)::(typing_pred_b)::[])::[]), ((xx)::(aa)::(bb)::[]), (uu____8821)))
in (mkForall_fuel' (Prims.parse_int "2") uu____8815))
in ((uu____8814), (Some ("ref typing is injective")), (Some ("ref_injectivity"))))
in FStar_SMTEncoding_Term.Assume (uu____8809))
in (uu____8808)::[])
in (uu____8773)::uu____8806))))))))))
in (

let mk_true_interp = (fun env nm true_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((true_tm)::[])))
in (FStar_SMTEncoding_Term.Assume (((valid), (Some ("True interpretation")), (Some ("true_interp")))))::[]))
in (

let mk_false_interp = (fun env nm false_tm -> (

let valid = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((false_tm)::[])))
in (

let uu____8875 = (

let uu____8876 = (

let uu____8881 = (FStar_SMTEncoding_Util.mkIff ((FStar_SMTEncoding_Util.mkFalse), (valid)))
in ((uu____8881), (Some ("False interpretation")), (Some ("false_interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8876))
in (uu____8875)::[])))
in (

let mk_and_interp = (fun env conj uu____8893 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____8903 = (

let uu____8907 = (

let uu____8909 = (FStar_SMTEncoding_Util.mkApp ((conj), ((a)::(b)::[])))
in (uu____8909)::[])
in (("Valid"), (uu____8907)))
in (FStar_SMTEncoding_Util.mkApp uu____8903))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____8916 = (

let uu____8917 = (

let uu____8922 = (

let uu____8923 = (

let uu____8929 = (

let uu____8930 = (

let uu____8933 = (FStar_SMTEncoding_Util.mkAnd ((valid_a), (valid_b)))
in ((uu____8933), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____8930))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____8929)))
in (FStar_SMTEncoding_Util.mkForall uu____8923))
in ((uu____8922), (Some ("/\\ interpretation")), (Some ("l_and-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8917))
in (uu____8916)::[])))))))))
in (

let mk_or_interp = (fun env disj uu____8958 -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let bb = (("b"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let b = (FStar_SMTEncoding_Util.mkFreeV bb)
in (

let valid = (

let uu____8968 = (

let uu____8972 = (

let uu____8974 = (FStar_SMTEncoding_Util.mkApp ((disj), ((a)::(b)::[])))
in (uu____8974)::[])
in (("Valid"), (uu____8972)))
in (FStar_SMTEncoding_Util.mkApp uu____8968))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____8981 = (

let uu____8982 = (

let uu____8987 = (

let uu____8988 = (

let uu____8994 = (

let uu____8995 = (

let uu____8998 = (FStar_SMTEncoding_Util.mkOr ((valid_a), (valid_b)))
in ((uu____8998), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____8995))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____8994)))
in (FStar_SMTEncoding_Util.mkForall uu____8988))
in ((uu____8987), (Some ("\\/ interpretation")), (Some ("l_or-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____8982))
in (uu____8981)::[])))))))))
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

let uu____9037 = (

let uu____9041 = (

let uu____9043 = (FStar_SMTEncoding_Util.mkApp ((eq2), ((a)::(x)::(y)::[])))
in (uu____9043)::[])
in (("Valid"), (uu____9041)))
in (FStar_SMTEncoding_Util.mkApp uu____9037))
in (

let uu____9046 = (

let uu____9047 = (

let uu____9052 = (

let uu____9053 = (

let uu____9059 = (

let uu____9060 = (

let uu____9063 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((uu____9063), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9060))
in ((((valid)::[])::[]), ((aa)::(xx)::(yy)::[]), (uu____9059)))
in (FStar_SMTEncoding_Util.mkForall uu____9053))
in ((uu____9052), (Some ("Eq2 interpretation")), (Some ("eq2-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9047))
in (uu____9046)::[])))))))))
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

let uu____9108 = (

let uu____9112 = (

let uu____9114 = (FStar_SMTEncoding_Util.mkApp ((eq3), ((a)::(b)::(x)::(y)::[])))
in (uu____9114)::[])
in (("Valid"), (uu____9112)))
in (FStar_SMTEncoding_Util.mkApp uu____9108))
in (

let uu____9117 = (

let uu____9118 = (

let uu____9123 = (

let uu____9124 = (

let uu____9130 = (

let uu____9131 = (

let uu____9134 = (FStar_SMTEncoding_Util.mkEq ((x), (y)))
in ((uu____9134), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9131))
in ((((valid)::[])::[]), ((aa)::(bb)::(xx)::(yy)::[]), (uu____9130)))
in (FStar_SMTEncoding_Util.mkForall uu____9124))
in ((uu____9123), (Some ("Eq3 interpretation")), (Some ("eq3-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9118))
in (uu____9117)::[])))))))))))
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

let uu____9173 = (

let uu____9177 = (

let uu____9179 = (FStar_SMTEncoding_Util.mkApp ((imp), ((a)::(b)::[])))
in (uu____9179)::[])
in (("Valid"), (uu____9177)))
in (FStar_SMTEncoding_Util.mkApp uu____9173))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9186 = (

let uu____9187 = (

let uu____9192 = (

let uu____9193 = (

let uu____9199 = (

let uu____9200 = (

let uu____9203 = (FStar_SMTEncoding_Util.mkImp ((valid_a), (valid_b)))
in ((uu____9203), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9200))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9199)))
in (FStar_SMTEncoding_Util.mkForall uu____9193))
in ((uu____9192), (Some ("==> interpretation")), (Some ("l_imp-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9187))
in (uu____9186)::[])))))))))
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

let uu____9238 = (

let uu____9242 = (

let uu____9244 = (FStar_SMTEncoding_Util.mkApp ((iff), ((a)::(b)::[])))
in (uu____9244)::[])
in (("Valid"), (uu____9242)))
in (FStar_SMTEncoding_Util.mkApp uu____9238))
in (

let valid_a = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (

let valid_b = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((b)::[])))
in (

let uu____9251 = (

let uu____9252 = (

let uu____9257 = (

let uu____9258 = (

let uu____9264 = (

let uu____9265 = (

let uu____9268 = (FStar_SMTEncoding_Util.mkIff ((valid_a), (valid_b)))
in ((uu____9268), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9265))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9264)))
in (FStar_SMTEncoding_Util.mkForall uu____9258))
in ((uu____9257), (Some ("<==> interpretation")), (Some ("l_iff-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9252))
in (uu____9251)::[])))))))))
in (

let mk_not_interp = (fun env l_not tt -> (

let aa = (("a"), (FStar_SMTEncoding_Term.Term_sort))
in (

let a = (FStar_SMTEncoding_Util.mkFreeV aa)
in (

let valid = (

let uu____9299 = (

let uu____9303 = (

let uu____9305 = (FStar_SMTEncoding_Util.mkApp ((l_not), ((a)::[])))
in (uu____9305)::[])
in (("Valid"), (uu____9303)))
in (FStar_SMTEncoding_Util.mkApp uu____9299))
in (

let not_valid_a = (

let uu____9309 = (FStar_SMTEncoding_Util.mkApp (("Valid"), ((a)::[])))
in (FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9309))
in (

let uu____9311 = (

let uu____9312 = (

let uu____9317 = (

let uu____9318 = (

let uu____9324 = (FStar_SMTEncoding_Util.mkIff ((not_valid_a), (valid)))
in ((((valid)::[])::[]), ((aa)::[]), (uu____9324)))
in (FStar_SMTEncoding_Util.mkForall uu____9318))
in ((uu____9317), (Some ("not interpretation")), (Some ("l_not-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9312))
in (uu____9311)::[]))))))
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

let uu____9361 = (

let uu____9365 = (

let uu____9367 = (FStar_SMTEncoding_Util.mkApp ((for_all), ((a)::(b)::[])))
in (uu____9367)::[])
in (("Valid"), (uu____9365)))
in (FStar_SMTEncoding_Util.mkApp uu____9361))
in (

let valid_b_x = (

let uu____9371 = (

let uu____9375 = (

let uu____9377 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (uu____9377)::[])
in (("Valid"), (uu____9375)))
in (FStar_SMTEncoding_Util.mkApp uu____9371))
in (

let uu____9379 = (

let uu____9380 = (

let uu____9385 = (

let uu____9386 = (

let uu____9392 = (

let uu____9393 = (

let uu____9396 = (

let uu____9397 = (

let uu____9403 = (

let uu____9406 = (

let uu____9408 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (uu____9408)::[])
in (uu____9406)::[])
in (

let uu____9411 = (

let uu____9412 = (

let uu____9415 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((uu____9415), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9412))
in ((uu____9403), ((xx)::[]), (uu____9411))))
in (FStar_SMTEncoding_Util.mkForall uu____9397))
in ((uu____9396), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9393))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9392)))
in (FStar_SMTEncoding_Util.mkForall uu____9386))
in ((uu____9385), (Some ("forall interpretation")), (Some ("forall-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9380))
in (uu____9379)::[]))))))))))
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

let uu____9463 = (

let uu____9467 = (

let uu____9469 = (FStar_SMTEncoding_Util.mkApp ((for_some), ((a)::(b)::[])))
in (uu____9469)::[])
in (("Valid"), (uu____9467)))
in (FStar_SMTEncoding_Util.mkApp uu____9463))
in (

let valid_b_x = (

let uu____9473 = (

let uu____9477 = (

let uu____9479 = (FStar_SMTEncoding_Util.mk_ApplyTT b x)
in (uu____9479)::[])
in (("Valid"), (uu____9477)))
in (FStar_SMTEncoding_Util.mkApp uu____9473))
in (

let uu____9481 = (

let uu____9482 = (

let uu____9487 = (

let uu____9488 = (

let uu____9494 = (

let uu____9495 = (

let uu____9498 = (

let uu____9499 = (

let uu____9505 = (

let uu____9508 = (

let uu____9510 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in (uu____9510)::[])
in (uu____9508)::[])
in (

let uu____9513 = (

let uu____9514 = (

let uu____9517 = (FStar_SMTEncoding_Term.mk_HasTypeZ x a)
in ((uu____9517), (valid_b_x)))
in (FStar_SMTEncoding_Util.mkImp uu____9514))
in ((uu____9505), ((xx)::[]), (uu____9513))))
in (FStar_SMTEncoding_Util.mkExists uu____9499))
in ((uu____9498), (valid)))
in (FStar_SMTEncoding_Util.mkIff uu____9495))
in ((((valid)::[])::[]), ((aa)::(bb)::[]), (uu____9494)))
in (FStar_SMTEncoding_Util.mkForall uu____9488))
in ((uu____9487), (Some ("exists interpretation")), (Some ("exists-interp"))))
in FStar_SMTEncoding_Term.Assume (uu____9482))
in (uu____9481)::[]))))))))))
in (

let mk_range_interp = (fun env range tt -> (

let range_ty = (FStar_SMTEncoding_Util.mkApp ((range), ([])))
in (

let uu____9554 = (

let uu____9555 = (

let uu____9560 = (FStar_SMTEncoding_Term.mk_HasTypeZ FStar_SMTEncoding_Term.mk_Range_const range_ty)
in (

let uu____9561 = (

let uu____9563 = (varops.mk_unique "typing_range_const")
in Some (uu____9563))
in ((uu____9560), (Some ("Range_const typing")), (uu____9561))))
in FStar_SMTEncoding_Term.Assume (uu____9555))
in (uu____9554)::[])))
in (

let prims = (((FStar_Syntax_Const.unit_lid), (mk_unit)))::(((FStar_Syntax_Const.bool_lid), (mk_bool)))::(((FStar_Syntax_Const.int_lid), (mk_int)))::(((FStar_Syntax_Const.string_lid), (mk_str)))::(((FStar_Syntax_Const.ref_lid), (mk_ref)))::(((FStar_Syntax_Const.true_lid), (mk_true_interp)))::(((FStar_Syntax_Const.false_lid), (mk_false_interp)))::(((FStar_Syntax_Const.and_lid), (mk_and_interp)))::(((FStar_Syntax_Const.or_lid), (mk_or_interp)))::(((FStar_Syntax_Const.eq2_lid), (mk_eq2_interp)))::(((FStar_Syntax_Const.eq3_lid), (mk_eq3_interp)))::(((FStar_Syntax_Const.imp_lid), (mk_imp_interp)))::(((FStar_Syntax_Const.iff_lid), (mk_iff_interp)))::(((FStar_Syntax_Const.not_lid), (mk_not_interp)))::(((FStar_Syntax_Const.forall_lid), (mk_forall_interp)))::(((FStar_Syntax_Const.exists_lid), (mk_exists_interp)))::(((FStar_Syntax_Const.range_lid), (mk_range_interp)))::[]
in (fun env t s tt -> (

let uu____9826 = (FStar_Util.find_opt (fun uu____9844 -> (match (uu____9844) with
| (l, uu____9854) -> begin
(FStar_Ident.lid_equals l t)
end)) prims)
in (match (uu____9826) with
| None -> begin
[]
end
| Some (uu____9876, f) -> begin
(f env s tt)
end)))))))))))))))))))))))))


let encode_smt_lemma : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun env fv t -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9913 = (encode_function_type_as_formula None None t env)
in (match (uu____9913) with
| (form, decls) -> begin
(FStar_List.append decls ((FStar_SMTEncoding_Term.Assume (((form), (Some ((Prims.strcat "Lemma: " lid.FStar_Ident.str))), (Some ((Prims.strcat "lemma_" lid.FStar_Ident.str))))))::[]))
end))))


let encode_free_var : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env fv tt t_norm quals -> (

let lid = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____9946 = ((

let uu____9947 = (FStar_Syntax_Util.is_pure_or_ghost_function t_norm)
in (FStar_All.pipe_left Prims.op_Negation uu____9947)) || (FStar_Syntax_Util.is_lemma t_norm))
in (match (uu____9946) with
| true -> begin
(

let uu____9951 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____9951) with
| (vname, vtok, env) -> begin
(

let arg_sorts = (

let uu____9963 = (

let uu____9964 = (FStar_Syntax_Subst.compress t_norm)
in uu____9964.FStar_Syntax_Syntax.n)
in (match (uu____9963) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____9969) -> begin
(FStar_All.pipe_right binders (FStar_List.map (fun uu____9986 -> FStar_SMTEncoding_Term.Term_sort)))
end
| uu____9989 -> begin
[]
end))
in (

let d = FStar_SMTEncoding_Term.DeclFun (((vname), (arg_sorts), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted function symbol for impure function"))))
in (

let dd = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Uninterpreted name for impure function"))))
in (((d)::(dd)::[]), (env)))))
end))
end
| uu____9997 -> begin
(

let uu____9998 = (prims.is lid)
in (match (uu____9998) with
| true -> begin
(

let vname = (varops.new_fvar lid)
in (

let uu____10003 = (prims.mk lid vname)
in (match (uu____10003) with
| (tok, definition) -> begin
(

let env = (push_free_var env lid vname (Some (tok)))
in ((definition), (env)))
end)))
end
| uu____10016 -> begin
(

let encode_non_total_function_typ = (lid.FStar_Ident.nsstr <> "Prims")
in (

let uu____10018 = (

let uu____10024 = (curried_arrow_formals_comp t_norm)
in (match (uu____10024) with
| (args, comp) -> begin
(match (encode_non_total_function_typ) with
| true -> begin
(

let uu____10039 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post env.tcenv comp)
in ((args), (uu____10039)))
end
| uu____10046 -> begin
((args), (((None), ((FStar_Syntax_Util.comp_result comp)))))
end)
end))
in (match (uu____10018) with
| (formals, (pre_opt, res_t)) -> begin
(

let uu____10066 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____10066) with
| (vname, vtok, env) -> begin
(

let vtok_tm = (match (formals) with
| [] -> begin
(FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
end
| uu____10079 -> begin
(FStar_SMTEncoding_Util.mkApp ((vtok), ([])))
end)
in (

let mk_disc_proj_axioms = (fun guard encoded_res_t vapp vars -> (FStar_All.pipe_right quals (FStar_List.collect (fun uu___123_10103 -> (match (uu___123_10103) with
| FStar_Syntax_Syntax.Discriminator (d) -> begin
(

let uu____10106 = (FStar_Util.prefix vars)
in (match (uu____10106) with
| (uu____10117, (xxsym, uu____10119)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____10129 = (

let uu____10130 = (

let uu____10135 = (

let uu____10136 = (

let uu____10142 = (

let uu____10143 = (

let uu____10146 = (

let uu____10147 = (FStar_SMTEncoding_Term.mk_tester (escape d.FStar_Ident.str) xx)
in (FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool uu____10147))
in ((vapp), (uu____10146)))
in (FStar_SMTEncoding_Util.mkEq uu____10143))
in ((((vapp)::[])::[]), (vars), (uu____10142)))
in (FStar_SMTEncoding_Util.mkForall uu____10136))
in ((uu____10135), (Some ("Discriminator equation")), (Some ((Prims.strcat "disc_equation_" (escape d.FStar_Ident.str))))))
in FStar_SMTEncoding_Term.Assume (uu____10130))
in (uu____10129)::[]))
end))
end
| FStar_Syntax_Syntax.Projector (d, f) -> begin
(

let uu____10159 = (FStar_Util.prefix vars)
in (match (uu____10159) with
| (uu____10170, (xxsym, uu____10172)) -> begin
(

let xx = (FStar_SMTEncoding_Util.mkFreeV ((xxsym), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = {FStar_Syntax_Syntax.ppname = f; FStar_Syntax_Syntax.index = (Prims.parse_int "0"); FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun}
in (

let tp_name = (mk_term_projector_name d f)
in (

let prim_app = (FStar_SMTEncoding_Util.mkApp ((tp_name), ((xx)::[])))
in (

let uu____10186 = (

let uu____10187 = (

let uu____10192 = (

let uu____10193 = (

let uu____10199 = (FStar_SMTEncoding_Util.mkEq ((vapp), (prim_app)))
in ((((vapp)::[])::[]), (vars), (uu____10199)))
in (FStar_SMTEncoding_Util.mkForall uu____10193))
in ((uu____10192), (Some ("Projector equation")), (Some ((Prims.strcat "proj_equation_" tp_name)))))
in FStar_SMTEncoding_Term.Assume (uu____10187))
in (uu____10186)::[])))))
end))
end
| uu____10209 -> begin
[]
end)))))
in (

let uu____10210 = (encode_binders None formals env)
in (match (uu____10210) with
| (vars, guards, env', decls1, uu____10226) -> begin
(

let uu____10233 = (match (pre_opt) with
| None -> begin
(

let uu____10238 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____10238), (decls1)))
end
| Some (p) -> begin
(

let uu____10240 = (encode_formula p env')
in (match (uu____10240) with
| (g, ds) -> begin
(

let uu____10247 = (FStar_SMTEncoding_Util.mk_and_l ((g)::guards))
in ((uu____10247), ((FStar_List.append decls1 ds))))
end))
end)
in (match (uu____10233) with
| (guard, decls1) -> begin
(

let vtok_app = (mk_Apply vtok_tm vars)
in (

let vapp = (

let uu____10256 = (

let uu____10260 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((vname), (uu____10260)))
in (FStar_SMTEncoding_Util.mkApp uu____10256))
in (

let uu____10265 = (

let vname_decl = (

let uu____10270 = (

let uu____10276 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____10281 -> FStar_SMTEncoding_Term.Term_sort)))
in ((vname), (uu____10276), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____10270))
in (

let uu____10286 = (

let env = (

let uu___151_10290 = env
in {bindings = uu___151_10290.bindings; depth = uu___151_10290.depth; tcenv = uu___151_10290.tcenv; warn = uu___151_10290.warn; cache = uu___151_10290.cache; nolabels = uu___151_10290.nolabels; use_zfuel_name = uu___151_10290.use_zfuel_name; encode_non_total_function_typ = encode_non_total_function_typ})
in (

let uu____10291 = (

let uu____10292 = (head_normal env tt)
in (not (uu____10292)))
in (match (uu____10291) with
| true -> begin
(encode_term_pred None tt env vtok_tm)
end
| uu____10295 -> begin
(encode_term_pred None t_norm env vtok_tm)
end)))
in (match (uu____10286) with
| (tok_typing, decls2) -> begin
(

let tok_typing = FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("function token typing")), (Some ((Prims.strcat "function_token_typing_" vname)))))
in (

let uu____10304 = (match (formals) with
| [] -> begin
(

let uu____10313 = (

let uu____10314 = (

let uu____10316 = (FStar_SMTEncoding_Util.mkFreeV ((vname), (FStar_SMTEncoding_Term.Term_sort)))
in (FStar_All.pipe_left (fun _0_34 -> Some (_0_34)) uu____10316))
in (push_free_var env lid vname uu____10314))
in (((FStar_List.append decls2 ((tok_typing)::[]))), (uu____10313)))
end
| uu____10319 -> begin
(

let vtok_decl = FStar_SMTEncoding_Term.DeclFun (((vtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (None)))
in (

let vtok_fresh = (

let uu____10324 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((vtok), (FStar_SMTEncoding_Term.Term_sort)) uu____10324))
in (

let name_tok_corr = (

let uu____10326 = (

let uu____10331 = (

let uu____10332 = (

let uu____10338 = (FStar_SMTEncoding_Util.mkEq ((vtok_app), (vapp)))
in ((((vtok_app)::[])::((vapp)::[])::[]), (vars), (uu____10338)))
in (FStar_SMTEncoding_Util.mkForall uu____10332))
in ((uu____10331), (Some ("Name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" vname)))))
in FStar_SMTEncoding_Term.Assume (uu____10326))
in (((FStar_List.append decls2 ((vtok_decl)::(vtok_fresh)::(name_tok_corr)::(tok_typing)::[]))), (env)))))
end)
in (match (uu____10304) with
| (tok_decl, env) -> begin
(((vname_decl)::tok_decl), (env))
end)))
end)))
in (match (uu____10265) with
| (decls2, env) -> begin
(

let uu____10363 = (

let res_t = (FStar_Syntax_Subst.compress res_t)
in (

let uu____10368 = (encode_term res_t env')
in (match (uu____10368) with
| (encoded_res_t, decls) -> begin
(

let uu____10376 = (FStar_SMTEncoding_Term.mk_HasType vapp encoded_res_t)
in ((encoded_res_t), (uu____10376), (decls)))
end)))
in (match (uu____10363) with
| (encoded_res_t, ty_pred, decls3) -> begin
(

let typingAx = (

let uu____10384 = (

let uu____10389 = (

let uu____10390 = (

let uu____10396 = (FStar_SMTEncoding_Util.mkImp ((guard), (ty_pred)))
in ((((vapp)::[])::[]), (vars), (uu____10396)))
in (FStar_SMTEncoding_Util.mkForall uu____10390))
in ((uu____10389), (Some ("free var typing")), (Some ((Prims.strcat "typing_" vname)))))
in FStar_SMTEncoding_Term.Assume (uu____10384))
in (

let freshness = (

let uu____10406 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.New))
in (match (uu____10406) with
| true -> begin
(

let uu____10409 = (

let uu____10410 = (

let uu____10416 = (FStar_All.pipe_right vars (FStar_List.map Prims.snd))
in (

let uu____10422 = (varops.next_id ())
in ((vname), (uu____10416), (FStar_SMTEncoding_Term.Term_sort), (uu____10422))))
in (FStar_SMTEncoding_Term.fresh_constructor uu____10410))
in (

let uu____10424 = (

let uu____10426 = (pretype_axiom vapp vars)
in (uu____10426)::[])
in (uu____10409)::uu____10424))
end
| uu____10427 -> begin
[]
end))
in (

let g = (

let uu____10430 = (

let uu____10432 = (

let uu____10434 = (

let uu____10436 = (

let uu____10438 = (mk_disc_proj_axioms guard encoded_res_t vapp vars)
in (typingAx)::uu____10438)
in (FStar_List.append freshness uu____10436))
in (FStar_List.append decls3 uu____10434))
in (FStar_List.append decls2 uu____10432))
in (FStar_List.append decls1 uu____10430))
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

let uu____10460 = (try_lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10460) with
| None -> begin
(

let uu____10483 = (encode_free_var env x t t_norm [])
in (match (uu____10483) with
| (decls, env) -> begin
(

let uu____10498 = (lookup_lid env x.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____10498) with
| (n, x', uu____10517) -> begin
((((n), (x'))), (decls), (env))
end))
end))
end
| Some (n, x, uu____10529) -> begin
((((n), (x))), ([]), (env))
end)))


let encode_top_level_val : env_t  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env lid t quals -> (

let tt = (norm env t)
in (

let uu____10562 = (encode_free_var env lid t tt quals)
in (match (uu____10562) with
| (decls, env) -> begin
(

let uu____10573 = (FStar_Syntax_Util.is_smt_lemma t)
in (match (uu____10573) with
| true -> begin
(

let uu____10577 = (

let uu____10579 = (encode_smt_lemma env lid tt)
in (FStar_List.append decls uu____10579))
in ((uu____10577), (env)))
end
| uu____10582 -> begin
((decls), (env))
end))
end))))


let encode_top_level_vals : env_t  ->  FStar_Syntax_Syntax.letbinding Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env bindings quals -> (FStar_All.pipe_right bindings (FStar_List.fold_left (fun uu____10607 lb -> (match (uu____10607) with
| (decls, env) -> begin
(

let uu____10619 = (

let uu____10623 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (encode_top_level_val env uu____10623 lb.FStar_Syntax_Syntax.lbtyp quals))
in (match (uu____10619) with
| (decls', env) -> begin
(((FStar_List.append decls decls')), (env))
end))
end)) (([]), (env)))))


let encode_top_level_let : env_t  ->  (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env uu____10647 quals -> (match (uu____10647) with
| (is_rec, bindings) -> begin
(

let eta_expand = (fun binders formals body t -> (

let nbinders = (FStar_List.length binders)
in (

let uu____10696 = (FStar_Util.first_N nbinders formals)
in (match (uu____10696) with
| (formals, extra_formals) -> begin
(

let subst = (FStar_List.map2 (fun uu____10736 uu____10737 -> (match (((uu____10736), (uu____10737))) with
| ((formal, uu____10747), (binder, uu____10749)) -> begin
(

let uu____10754 = (

let uu____10759 = (FStar_Syntax_Syntax.bv_to_name binder)
in ((formal), (uu____10759)))
in FStar_Syntax_Syntax.NT (uu____10754))
end)) formals binders)
in (

let extra_formals = (

let uu____10764 = (FStar_All.pipe_right extra_formals (FStar_List.map (fun uu____10778 -> (match (uu____10778) with
| (x, i) -> begin
(

let uu____10785 = (

let uu___152_10786 = x
in (

let uu____10787 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = uu___152_10786.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___152_10786.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = uu____10787}))
in ((uu____10785), (i)))
end))))
in (FStar_All.pipe_right uu____10764 FStar_Syntax_Util.name_binders))
in (

let body = (

let uu____10799 = (

let uu____10801 = (

let uu____10802 = (FStar_Syntax_Subst.subst subst t)
in uu____10802.FStar_Syntax_Syntax.n)
in (FStar_All.pipe_left (fun _0_35 -> Some (_0_35)) uu____10801))
in (

let uu____10806 = (

let uu____10807 = (FStar_Syntax_Subst.compress body)
in (

let uu____10808 = (

let uu____10809 = (FStar_Syntax_Util.args_of_binders extra_formals)
in (FStar_All.pipe_left Prims.snd uu____10809))
in (FStar_Syntax_Syntax.extend_app_n uu____10807 uu____10808)))
in (uu____10806 uu____10799 body.FStar_Syntax_Syntax.pos)))
in (((FStar_List.append binders extra_formals)), (body)))))
end))))
in (

let destruct_bound_function = (fun flid t_norm e -> (

let rec aux = (fun norm t_norm -> (

let uu____10868 = (FStar_Syntax_Util.abs_formals e)
in (match (uu____10868) with
| (binders, body, lopt) -> begin
(match (binders) with
| (uu____10921)::uu____10922 -> begin
(

let uu____10930 = (

let uu____10931 = (FStar_Syntax_Subst.compress t_norm)
in uu____10931.FStar_Syntax_Syntax.n)
in (match (uu____10930) with
| FStar_Syntax_Syntax.Tm_arrow (formals, c) -> begin
(

let uu____10960 = (FStar_Syntax_Subst.open_comp formals c)
in (match (uu____10960) with
| (formals, c) -> begin
(

let nformals = (FStar_List.length formals)
in (

let nbinders = (FStar_List.length binders)
in (

let tres = (FStar_Syntax_Util.comp_result c)
in (

let uu____10990 = ((nformals < nbinders) && (FStar_Syntax_Util.is_total_comp c))
in (match (uu____10990) with
| true -> begin
(

let uu____11010 = (FStar_Util.first_N nformals binders)
in (match (uu____11010) with
| (bs0, rest) -> begin
(

let c = (

let subst = (FStar_List.map2 (fun uu____11058 uu____11059 -> (match (((uu____11058), (uu____11059))) with
| ((x, uu____11069), (b, uu____11071)) -> begin
(

let uu____11076 = (

let uu____11081 = (FStar_Syntax_Syntax.bv_to_name b)
in ((x), (uu____11081)))
in FStar_Syntax_Syntax.NT (uu____11076))
end)) formals bs0)
in (FStar_Syntax_Subst.subst_comp subst c))
in (

let body = (FStar_Syntax_Util.abs rest body lopt)
in ((((bs0), (body), (bs0), ((FStar_Syntax_Util.comp_result c)))), (false))))
end))
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

let t_norm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.UnfoldUntil (FStar_Syntax_Syntax.Delta_constant))::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv t_norm)
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
end)
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

let uu____11663 = ((FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___124_11665 -> (match (uu___124_11665) with
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
| ((binders, body, uu____11746, uu____11747), curry) -> begin
((

let uu____11754 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____11754) with
| true -> begin
(

let uu____11755 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____11756 = (FStar_Syntax_Print.term_to_string body)
in (FStar_Util.print2 "Encoding let : binders=[%s], body=%s\n" uu____11755 uu____11756)))
end
| uu____11757 -> begin
()
end));
(

let uu____11758 = (encode_binders None binders env)
in (match (uu____11758) with
| (vars, guards, env', binder_decls, uu____11774) -> begin
(

let app = (mk_app curry f ftok vars)
in (

let uu____11782 = (

let uu____11787 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Logic))
in (match (uu____11787) with
| true -> begin
(

let uu____11793 = (FStar_SMTEncoding_Term.mk_Valid app)
in (

let uu____11794 = (encode_formula body env')
in ((uu____11793), (uu____11794))))
end
| uu____11799 -> begin
(

let uu____11800 = (encode_term body env')
in ((app), (uu____11800)))
end))
in (match (uu____11782) with
| (app, (body, decls2)) -> begin
(

let eqn = (

let uu____11814 = (

let uu____11819 = (

let uu____11820 = (

let uu____11826 = (FStar_SMTEncoding_Util.mkEq ((app), (body)))
in ((((app)::[])::[]), (vars), (uu____11826)))
in (FStar_SMTEncoding_Util.mkForall uu____11820))
in (

let uu____11832 = (

let uu____11834 = (FStar_Util.format1 "Equation for %s" flid.FStar_Ident.str)
in Some (uu____11834))
in ((uu____11819), (uu____11832), (Some ((Prims.strcat "equation_" f))))))
in FStar_SMTEncoding_Term.Assume (uu____11814))
in (

let uu____11837 = (

let uu____11839 = (

let uu____11841 = (

let uu____11843 = (

let uu____11845 = (primitive_type_axioms env.tcenv flid f app)
in (FStar_List.append ((eqn)::[]) uu____11845))
in (FStar_List.append decls2 uu____11843))
in (FStar_List.append binder_decls uu____11841))
in (FStar_List.append decls uu____11839))
in ((uu____11837), (env))))
end)))
end));
)
end))))
end
| uu____11848 -> begin
(failwith "Impossible")
end)
end
| uu____11863 -> begin
(

let fuel = (

let uu____11867 = (varops.fresh "fuel")
in ((uu____11867), (FStar_SMTEncoding_Term.Fuel_sort)))
in (

let fuel_tm = (FStar_SMTEncoding_Util.mkFreeV fuel)
in (

let env0 = env
in (

let uu____11870 = (FStar_All.pipe_right toks (FStar_List.fold_left (fun uu____11909 uu____11910 -> (match (((uu____11909), (uu____11910))) with
| ((gtoks, env), (flid_fv, (f, ftok))) -> begin
(

let flid = flid_fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let g = (

let uu____11992 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented")
in (varops.new_fvar uu____11992))
in (

let gtok = (

let uu____11994 = (FStar_Ident.lid_add_suffix flid "fuel_instrumented_token")
in (varops.new_fvar uu____11994))
in (

let env = (

let uu____11996 = (

let uu____11998 = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::[])))
in (FStar_All.pipe_left (fun _0_36 -> Some (_0_36)) uu____11998))
in (push_free_var env flid gtok uu____11996))
in (((((flid), (f), (ftok), (g), (gtok)))::gtoks), (env))))))
end)) (([]), (env))))
in (match (uu____11870) with
| (gtoks, env) -> begin
(

let gtoks = (FStar_List.rev gtoks)
in (

let encode_one_binding = (fun env0 uu____12082 t_norm uu____12084 -> (match (((uu____12082), (uu____12084))) with
| ((flid, f, ftok, g, gtok), {FStar_Syntax_Syntax.lbname = lbn; FStar_Syntax_Syntax.lbunivs = uu____12108; FStar_Syntax_Syntax.lbtyp = uu____12109; FStar_Syntax_Syntax.lbeff = uu____12110; FStar_Syntax_Syntax.lbdef = e}) -> begin
((

let uu____12128 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12128) with
| true -> begin
(

let uu____12129 = (FStar_Syntax_Print.lbname_to_string lbn)
in (

let uu____12130 = (FStar_Syntax_Print.term_to_string t_norm)
in (

let uu____12131 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.print3 "Encoding let rec %s : %s = %s\n" uu____12129 uu____12130 uu____12131))))
end
| uu____12132 -> begin
()
end));
(

let uu____12133 = (destruct_bound_function flid t_norm e)
in (match (uu____12133) with
| ((binders, body, formals, tres), curry) -> begin
((

let uu____12155 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env0.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12155) with
| true -> begin
(

let uu____12156 = (FStar_Syntax_Print.binders_to_string ", " binders)
in (

let uu____12157 = (FStar_Syntax_Print.term_to_string body)
in (

let uu____12158 = (FStar_Syntax_Print.binders_to_string ", " formals)
in (

let uu____12159 = (FStar_Syntax_Print.term_to_string tres)
in (FStar_Util.print4 "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n" uu____12156 uu____12157 uu____12158 uu____12159)))))
end
| uu____12160 -> begin
()
end));
(match (curry) with
| true -> begin
(failwith "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type")
end
| uu____12162 -> begin
()
end);
(

let uu____12163 = (encode_binders None binders env)
in (match (uu____12163) with
| (vars, guards, env', binder_decls, uu____12181) -> begin
(

let decl_g = (

let uu____12189 = (

let uu____12195 = (

let uu____12197 = (FStar_List.map Prims.snd vars)
in (FStar_SMTEncoding_Term.Fuel_sort)::uu____12197)
in ((g), (uu____12195), (FStar_SMTEncoding_Term.Term_sort), (Some ("Fuel-instrumented function name"))))
in FStar_SMTEncoding_Term.DeclFun (uu____12189))
in (

let env0 = (push_zfuel_name env0 flid g)
in (

let decl_g_tok = FStar_SMTEncoding_Term.DeclFun (((gtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Token for fuel-instrumented partial applications"))))
in (

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let app = (

let uu____12212 = (

let uu____12216 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((f), (uu____12216)))
in (FStar_SMTEncoding_Util.mkApp uu____12212))
in (

let gsapp = (

let uu____12222 = (

let uu____12226 = (

let uu____12228 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (uu____12228)::vars_tm)
in ((g), (uu____12226)))
in (FStar_SMTEncoding_Util.mkApp uu____12222))
in (

let gmax = (

let uu____12232 = (

let uu____12236 = (

let uu____12238 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (uu____12238)::vars_tm)
in ((g), (uu____12236)))
in (FStar_SMTEncoding_Util.mkApp uu____12232))
in (

let uu____12241 = (encode_term body env')
in (match (uu____12241) with
| (body_tm, decls2) -> begin
(

let eqn_g = (

let uu____12252 = (

let uu____12257 = (

let uu____12258 = (

let uu____12266 = (FStar_SMTEncoding_Util.mkEq ((gsapp), (body_tm)))
in ((((gsapp)::[])::[]), (Some ((Prims.parse_int "0"))), ((fuel)::vars), (uu____12266)))
in (FStar_SMTEncoding_Util.mkForall' uu____12258))
in (

let uu____12277 = (

let uu____12279 = (FStar_Util.format1 "Equation for fuel-instrumented recursive function: %s" flid.FStar_Ident.str)
in Some (uu____12279))
in ((uu____12257), (uu____12277), (Some ((Prims.strcat "equation_with_fuel_" g))))))
in FStar_SMTEncoding_Term.Assume (uu____12252))
in (

let eqn_f = (

let uu____12283 = (

let uu____12288 = (

let uu____12289 = (

let uu____12295 = (FStar_SMTEncoding_Util.mkEq ((app), (gmax)))
in ((((app)::[])::[]), (vars), (uu____12295)))
in (FStar_SMTEncoding_Util.mkForall uu____12289))
in ((uu____12288), (Some ("Correspondence of recursive function to instrumented version")), (Some ((Prims.strcat "fuel_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12283))
in (

let eqn_g' = (

let uu____12304 = (

let uu____12309 = (

let uu____12310 = (

let uu____12316 = (

let uu____12317 = (

let uu____12320 = (

let uu____12321 = (

let uu____12325 = (

let uu____12327 = (FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0"))
in (uu____12327)::vars_tm)
in ((g), (uu____12325)))
in (FStar_SMTEncoding_Util.mkApp uu____12321))
in ((gsapp), (uu____12320)))
in (FStar_SMTEncoding_Util.mkEq uu____12317))
in ((((gsapp)::[])::[]), ((fuel)::vars), (uu____12316)))
in (FStar_SMTEncoding_Util.mkForall uu____12310))
in ((uu____12309), (Some ("Fuel irrelevance")), (Some ((Prims.strcat "fuel_irrelevance_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12304))
in (

let uu____12340 = (

let uu____12345 = (encode_binders None formals env0)
in (match (uu____12345) with
| (vars, v_guards, env, binder_decls, uu____12362) -> begin
(

let vars_tm = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let gapp = (FStar_SMTEncoding_Util.mkApp ((g), ((fuel_tm)::vars_tm)))
in (

let tok_corr = (

let tok_app = (

let uu____12377 = (FStar_SMTEncoding_Util.mkFreeV ((gtok), (FStar_SMTEncoding_Term.Term_sort)))
in (mk_Apply uu____12377 ((fuel)::vars)))
in (

let uu____12380 = (

let uu____12385 = (

let uu____12386 = (

let uu____12392 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (gapp)))
in ((((tok_app)::[])::[]), ((fuel)::vars), (uu____12392)))
in (FStar_SMTEncoding_Util.mkForall uu____12386))
in ((uu____12385), (Some ("Fuel token correspondence")), (Some ((Prims.strcat "fuel_token_correspondence_" gtok)))))
in FStar_SMTEncoding_Term.Assume (uu____12380)))
in (

let uu____12404 = (

let uu____12408 = (encode_term_pred None tres env gapp)
in (match (uu____12408) with
| (g_typing, d3) -> begin
(

let uu____12416 = (

let uu____12418 = (

let uu____12419 = (

let uu____12424 = (

let uu____12425 = (

let uu____12431 = (

let uu____12432 = (

let uu____12435 = (FStar_SMTEncoding_Util.mk_and_l v_guards)
in ((uu____12435), (g_typing)))
in (FStar_SMTEncoding_Util.mkImp uu____12432))
in ((((gapp)::[])::[]), ((fuel)::vars), (uu____12431)))
in (FStar_SMTEncoding_Util.mkForall uu____12425))
in ((uu____12424), (Some ("Typing correspondence of token to term")), (Some ((Prims.strcat "token_correspondence_" g)))))
in FStar_SMTEncoding_Term.Assume (uu____12419))
in (uu____12418)::[])
in ((d3), (uu____12416)))
end))
in (match (uu____12404) with
| (aux_decls, typing_corr) -> begin
(((FStar_List.append binder_decls aux_decls)), ((FStar_List.append typing_corr ((tok_corr)::[]))))
end)))))
end))
in (match (uu____12340) with
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

let uu____12471 = (

let uu____12478 = (FStar_List.zip3 gtoks typs bindings)
in (FStar_List.fold_left (fun uu____12510 uu____12511 -> (match (((uu____12510), (uu____12511))) with
| ((decls, eqns, env0), (gtok, ty, lb)) -> begin
(

let uu____12587 = (encode_one_binding env0 gtok ty lb)
in (match (uu____12587) with
| (decls', eqns', env0) -> begin
(((decls')::decls), ((FStar_List.append eqns' eqns)), (env0))
end))
end)) (((decls)::[]), ([]), (env0)) uu____12478))
in (match (uu____12471) with
| (decls, eqns, env0) -> begin
(

let uu____12627 = (

let uu____12632 = (FStar_All.pipe_right decls FStar_List.flatten)
in (FStar_All.pipe_right uu____12632 (FStar_List.partition (fun uu___125_12642 -> (match (uu___125_12642) with
| FStar_SMTEncoding_Term.DeclFun (uu____12643) -> begin
true
end
| uu____12649 -> begin
false
end)))))
in (match (uu____12627) with
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

let uu____12667 = (FStar_All.pipe_right bindings (FStar_List.map (fun lb -> (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname))))
in (FStar_All.pipe_right uu____12667 (FStar_String.concat " and ")))
in (

let decl = FStar_SMTEncoding_Term.Caption ((Prims.strcat "let rec unencodeable: Skipping: " msg))
in (((decl)::[]), (env))))
end))
end))


let rec encode_sigelt : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> ((

let uu____12700 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____12700) with
| true -> begin
(

let uu____12701 = (FStar_Syntax_Print.sigelt_to_string se)
in (FStar_All.pipe_left (FStar_Util.print1 ">>>>Encoding [%s]\n") uu____12701))
end
| uu____12702 -> begin
()
end));
(

let nm = (

let uu____12704 = (FStar_Syntax_Util.lid_of_sigelt se)
in (match (uu____12704) with
| None -> begin
""
end
| Some (l) -> begin
l.FStar_Ident.str
end))
in (

let uu____12707 = (encode_sigelt' env se)
in (match (uu____12707) with
| (g, e) -> begin
(match (g) with
| [] -> begin
(

let uu____12716 = (

let uu____12718 = (

let uu____12719 = (FStar_Util.format1 "<Skipped %s/>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12719))
in (uu____12718)::[])
in ((uu____12716), (e)))
end
| uu____12721 -> begin
(

let uu____12722 = (

let uu____12724 = (

let uu____12726 = (

let uu____12727 = (FStar_Util.format1 "<Start encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12727))
in (uu____12726)::g)
in (

let uu____12728 = (

let uu____12730 = (

let uu____12731 = (FStar_Util.format1 "</end encoding %s>" nm)
in FStar_SMTEncoding_Term.Caption (uu____12731))
in (uu____12730)::[])
in (FStar_List.append uu____12724 uu____12728)))
in ((uu____12722), (e)))
end)
end)));
))
and encode_sigelt' : env_t  ->  FStar_Syntax_Syntax.sigelt  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env se -> (match (se) with
| FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____12739) -> begin
(failwith "impossible -- removed by tc.fs")
end
| (FStar_Syntax_Syntax.Sig_pragma (_)) | (FStar_Syntax_Syntax.Sig_main (_)) | (FStar_Syntax_Syntax.Sig_effect_abbrev (_)) | (FStar_Syntax_Syntax.Sig_sub_effect (_)) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_new_effect (ed, uu____12750) -> begin
(

let uu____12751 = (

let uu____12752 = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (FStar_All.pipe_right uu____12752 Prims.op_Negation))
in (match (uu____12751) with
| true -> begin
(([]), (env))
end
| uu____12757 -> begin
(

let close_effect_params = (fun tm -> (match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
tm
end
| uu____12772 -> begin
(

let uu____12773 = (

let uu____12776 = (

let uu____12777 = (

let uu____12792 = (FStar_All.pipe_left (fun _0_37 -> Some (_0_37)) (FStar_Util.Inr (((FStar_Syntax_Const.effect_Tot_lid), ((FStar_Syntax_Syntax.TOTAL)::[])))))
in ((ed.FStar_Syntax_Syntax.binders), (tm), (uu____12792)))
in FStar_Syntax_Syntax.Tm_abs (uu____12777))
in (FStar_Syntax_Syntax.mk uu____12776))
in (uu____12773 None tm.FStar_Syntax_Syntax.pos))
end))
in (

let encode_action = (fun env a -> (

let uu____12845 = (new_term_constant_and_tok_from_lid env a.FStar_Syntax_Syntax.action_name)
in (match (uu____12845) with
| (aname, atok, env) -> begin
(

let uu____12855 = (FStar_Syntax_Util.arrow_formals_comp a.FStar_Syntax_Syntax.action_typ)
in (match (uu____12855) with
| (formals, uu____12865) -> begin
(

let uu____12872 = (

let uu____12875 = (close_effect_params a.FStar_Syntax_Syntax.action_defn)
in (encode_term uu____12875 env))
in (match (uu____12872) with
| (tm, decls) -> begin
(

let a_decls = (

let uu____12883 = (

let uu____12884 = (

let uu____12890 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____12898 -> FStar_SMTEncoding_Term.Term_sort)))
in ((aname), (uu____12890), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action"))))
in FStar_SMTEncoding_Term.DeclFun (uu____12884))
in (uu____12883)::(FStar_SMTEncoding_Term.DeclFun (((atok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("Action token")))))::[])
in (

let uu____12905 = (

let uu____12912 = (FStar_All.pipe_right formals (FStar_List.map (fun uu____12932 -> (match (uu____12932) with
| (bv, uu____12940) -> begin
(

let uu____12941 = (gen_term_var env bv)
in (match (uu____12941) with
| (xxsym, xx, uu____12951) -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (xx))
end))
end))))
in (FStar_All.pipe_right uu____12912 FStar_List.split))
in (match (uu____12905) with
| (xs_sorts, xs) -> begin
(

let app = (

let uu____12981 = (

let uu____12985 = (

let uu____12987 = (FStar_SMTEncoding_Util.mkApp ((aname), (xs)))
in (uu____12987)::[])
in (("Reify"), (uu____12985)))
in (FStar_SMTEncoding_Util.mkApp uu____12981))
in (

let a_eq = (

let uu____12991 = (

let uu____12996 = (

let uu____12997 = (

let uu____13003 = (

let uu____13004 = (

let uu____13007 = (mk_Apply tm xs_sorts)
in ((app), (uu____13007)))
in (FStar_SMTEncoding_Util.mkEq uu____13004))
in ((((app)::[])::[]), (xs_sorts), (uu____13003)))
in (FStar_SMTEncoding_Util.mkForall uu____12997))
in ((uu____12996), (Some ("Action equality")), (Some ((Prims.strcat aname "_equality")))))
in FStar_SMTEncoding_Term.Assume (uu____12991))
in (

let tok_correspondence = (

let tok_term = (FStar_SMTEncoding_Util.mkFreeV ((atok), (FStar_SMTEncoding_Term.Term_sort)))
in (

let tok_app = (mk_Apply tok_term xs_sorts)
in (

let uu____13020 = (

let uu____13025 = (

let uu____13026 = (

let uu____13032 = (FStar_SMTEncoding_Util.mkEq ((tok_app), (app)))
in ((((tok_app)::[])::[]), (xs_sorts), (uu____13032)))
in (FStar_SMTEncoding_Util.mkForall uu____13026))
in ((uu____13025), (Some ("Action token correspondence")), (Some ((Prims.strcat aname "_token_correspondence")))))
in FStar_SMTEncoding_Term.Assume (uu____13020))))
in ((env), ((FStar_List.append decls (FStar_List.append a_decls ((a_eq)::(tok_correspondence)::[]))))))))
end)))
end))
end))
end)))
in (

let uu____13043 = (FStar_Util.fold_map encode_action env ed.FStar_Syntax_Syntax.actions)
in (match (uu____13043) with
| (env, decls2) -> begin
(((FStar_List.flatten decls2)), (env))
end))))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13059, uu____13060, uu____13061, uu____13062) when (FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid) -> begin
(

let uu____13065 = (new_term_constant_and_tok_from_lid env lid)
in (match (uu____13065) with
| (tname, ttok, env) -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____13076, t, quals, uu____13079) -> begin
(

let will_encode_definition = (

let uu____13083 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___126_13085 -> (match (uu___126_13085) with
| (FStar_Syntax_Syntax.Assumption) | (FStar_Syntax_Syntax.Projector (_)) | (FStar_Syntax_Syntax.Discriminator (_)) | (FStar_Syntax_Syntax.Irreducible) -> begin
true
end
| uu____13088 -> begin
false
end))))
in (not (uu____13083)))
in (match (will_encode_definition) with
| true -> begin
(([]), (env))
end
| uu____13092 -> begin
(

let fv = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____13094 = (encode_top_level_val env fv t quals)
in (match (uu____13094) with
| (decls, env) -> begin
(

let tname = lid.FStar_Ident.str
in (

let tsym = (FStar_SMTEncoding_Util.mkFreeV ((tname), (FStar_SMTEncoding_Term.Term_sort)))
in (

let uu____13106 = (

let uu____13108 = (primitive_type_axioms env.tcenv lid tname tsym)
in (FStar_List.append decls uu____13108))
in ((uu____13106), (env)))))
end)))
end))
end
| FStar_Syntax_Syntax.Sig_assume (l, f, uu____13113, uu____13114) -> begin
(

let uu____13117 = (encode_formula f env)
in (match (uu____13117) with
| (f, decls) -> begin
(

let g = (

let uu____13126 = (

let uu____13127 = (

let uu____13132 = (

let uu____13134 = (

let uu____13135 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Assumption: %s" uu____13135))
in Some (uu____13134))
in (

let uu____13136 = (

let uu____13138 = (varops.mk_unique (Prims.strcat "assumption_" l.FStar_Ident.str))
in Some (uu____13138))
in ((f), (uu____13132), (uu____13136))))
in FStar_SMTEncoding_Term.Assume (uu____13127))
in (uu____13126)::[])
in (((FStar_List.append decls g)), (env)))
end))
end
| FStar_Syntax_Syntax.Sig_let (lbs, r, uu____13144, quals, uu____13146) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Irreducible)) -> begin
(

let uu____13154 = (FStar_Util.fold_map (fun env lb -> (

let lid = (

let uu____13161 = (

let uu____13166 = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in uu____13166.FStar_Syntax_Syntax.fv_name)
in uu____13161.FStar_Syntax_Syntax.v)
in (

let uu____13170 = (

let uu____13171 = (FStar_TypeChecker_Env.try_lookup_val_decl env.tcenv lid)
in (FStar_All.pipe_left FStar_Option.isNone uu____13171))
in (match (uu____13170) with
| true -> begin
(

let val_decl = FStar_Syntax_Syntax.Sig_declare_typ (((lid), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), (r)))
in (

let uu____13190 = (encode_sigelt' env val_decl)
in (match (uu____13190) with
| (decls, env) -> begin
((env), (decls))
end)))
end
| uu____13197 -> begin
((env), ([]))
end)))) env (Prims.snd lbs))
in (match (uu____13154) with
| (env, decls) -> begin
(((FStar_List.flatten decls)), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((uu____13207, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (b2t); FStar_Syntax_Syntax.lbunivs = uu____13209; FStar_Syntax_Syntax.lbtyp = uu____13210; FStar_Syntax_Syntax.lbeff = uu____13211; FStar_Syntax_Syntax.lbdef = uu____13212})::[]), uu____13213, uu____13214, uu____13215, uu____13216) when (FStar_Syntax_Syntax.fv_eq_lid b2t FStar_Syntax_Const.b2t_lid) -> begin
(

let uu____13232 = (new_term_constant_and_tok_from_lid env b2t.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____13232) with
| (tname, ttok, env) -> begin
(

let xx = (("x"), (FStar_SMTEncoding_Term.Term_sort))
in (

let x = (FStar_SMTEncoding_Util.mkFreeV xx)
in (

let valid_b2t_x = (

let uu____13250 = (

let uu____13254 = (

let uu____13256 = (FStar_SMTEncoding_Util.mkApp (("Prims.b2t"), ((x)::[])))
in (uu____13256)::[])
in (("Valid"), (uu____13254)))
in (FStar_SMTEncoding_Util.mkApp uu____13250))
in (

let decls = (

let uu____13261 = (

let uu____13263 = (

let uu____13264 = (

let uu____13269 = (

let uu____13270 = (

let uu____13276 = (

let uu____13277 = (

let uu____13280 = (FStar_SMTEncoding_Util.mkApp (("BoxBool_proj_0"), ((x)::[])))
in ((valid_b2t_x), (uu____13280)))
in (FStar_SMTEncoding_Util.mkEq uu____13277))
in ((((valid_b2t_x)::[])::[]), ((xx)::[]), (uu____13276)))
in (FStar_SMTEncoding_Util.mkForall uu____13270))
in ((uu____13269), (Some ("b2t def")), (Some ("b2t_def"))))
in FStar_SMTEncoding_Term.Assume (uu____13264))
in (uu____13263)::[])
in (FStar_SMTEncoding_Term.DeclFun (((tname), ((FStar_SMTEncoding_Term.Term_sort)::[]), (FStar_SMTEncoding_Term.Term_sort), (None))))::uu____13261)
in ((decls), (env))))))
end))
end
| FStar_Syntax_Syntax.Sig_let (uu____13298, uu____13299, uu____13300, quals, uu____13302) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___127_13310 -> (match (uu___127_13310) with
| FStar_Syntax_Syntax.Discriminator (uu____13311) -> begin
true
end
| uu____13312 -> begin
false
end)))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let (uu____13314, uu____13315, lids, quals, uu____13318) when ((FStar_All.pipe_right lids (FStar_Util.for_some (fun l -> (

let uu____13327 = (

let uu____13328 = (FStar_List.hd l.FStar_Ident.ns)
in uu____13328.FStar_Ident.idText)
in (uu____13327 = "Prims"))))) && (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___128_13330 -> (match (uu___128_13330) with
| FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen -> begin
true
end
| uu____13331 -> begin
false
end))))) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_let ((false, (lb)::[]), uu____13334, uu____13335, quals, uu____13337) when (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___129_13349 -> (match (uu___129_13349) with
| FStar_Syntax_Syntax.Projector (uu____13350) -> begin
true
end
| uu____13353 -> begin
false
end)))) -> begin
(

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let l = fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v
in (

let uu____13360 = (try_lookup_free_var env l)
in (match (uu____13360) with
| Some (uu____13364) -> begin
(([]), (env))
end
| None -> begin
(

let se = FStar_Syntax_Syntax.Sig_declare_typ (((l), (lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp), (quals), ((FStar_Ident.range_of_lid l))))
in (encode_sigelt env se))
end))))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, (lb)::[]), uu____13373, uu____13374, quals, uu____13376) when (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) -> begin
(

let uu____13388 = (

let uu____13389 = (FStar_Syntax_Subst.compress lb.FStar_Syntax_Syntax.lbdef)
in uu____13389.FStar_Syntax_Syntax.n)
in (match (uu____13388) with
| FStar_Syntax_Syntax.Tm_abs (bs, body, uu____13396) -> begin
(

let body = (FStar_Syntax_Util.mk_reify body)
in (

let tm = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (body), (None))))) None lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.pos)
in (

let tm' = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Reify)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::[]) env.tcenv tm)
in (

let lb_typ = (

let uu____13453 = (FStar_Syntax_Util.arrow_formals_comp lb.FStar_Syntax_Syntax.lbtyp)
in (match (uu____13453) with
| (formals, comp) -> begin
(

let reified_typ = (FStar_TypeChecker_Util.reify_comp (

let uu___155_13470 = env.tcenv
in {FStar_TypeChecker_Env.solver = uu___155_13470.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___155_13470.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___155_13470.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___155_13470.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___155_13470.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___155_13470.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___155_13470.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___155_13470.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___155_13470.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___155_13470.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___155_13470.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___155_13470.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___155_13470.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___155_13470.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___155_13470.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___155_13470.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___155_13470.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___155_13470.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___155_13470.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.type_of = uu___155_13470.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___155_13470.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.use_bv_sorts = uu___155_13470.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qname_and_index = uu___155_13470.FStar_TypeChecker_Env.qname_and_index}) (FStar_Syntax_Util.lcomp_of_comp comp) FStar_Syntax_Syntax.U_unknown)
in (

let uu____13471 = (FStar_Syntax_Syntax.mk_Total reified_typ)
in (FStar_Syntax_Util.arrow formals uu____13471)))
end))
in (

let lb = (

let uu___156_13475 = lb
in {FStar_Syntax_Syntax.lbname = uu___156_13475.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = uu___156_13475.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = lb_typ; FStar_Syntax_Syntax.lbeff = uu___156_13475.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = tm'})
in ((

let uu____13477 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____13477) with
| true -> begin
(

let uu____13478 = (FStar_Syntax_Print.lbname_to_string lb.FStar_Syntax_Syntax.lbname)
in (

let uu____13479 = (FStar_Syntax_Print.term_to_string tm)
in (

let uu____13480 = (FStar_Syntax_Print.term_to_string tm')
in (FStar_Util.print3 "%s: Reified %s\nto %s\n" uu____13478 uu____13479 uu____13480))))
end
| uu____13481 -> begin
()
end));
(encode_top_level_let env ((is_rec), ((lb)::[])) quals);
))))))
end
| uu____13483 -> begin
(([]), (env))
end))
end
| FStar_Syntax_Syntax.Sig_let ((is_rec, bindings), uu____13487, uu____13488, quals, uu____13490) -> begin
(encode_top_level_let env ((is_rec), (bindings)) quals)
end
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____13504, uu____13505, uu____13506) -> begin
(

let uu____13513 = (encode_signature env ses)
in (match (uu____13513) with
| (g, env) -> begin
(

let uu____13523 = (FStar_All.pipe_right g (FStar_List.partition (fun uu___130_13533 -> (match (uu___130_13533) with
| FStar_SMTEncoding_Term.Assume (uu____13534, Some ("inversion axiom"), uu____13535) -> begin
false
end
| uu____13539 -> begin
true
end))))
in (match (uu____13523) with
| (g', inversions) -> begin
(

let uu____13548 = (FStar_All.pipe_right g' (FStar_List.partition (fun uu___131_13558 -> (match (uu___131_13558) with
| FStar_SMTEncoding_Term.DeclFun (uu____13559) -> begin
true
end
| uu____13565 -> begin
false
end))))
in (match (uu____13548) with
| (decls, rest) -> begin
(((FStar_List.append decls (FStar_List.append rest inversions))), (env))
end))
end))
end))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (t, uu____13576, tps, k, uu____13579, datas, quals, uu____13582) -> begin
(

let is_logical = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___132_13591 -> (match (uu___132_13591) with
| (FStar_Syntax_Syntax.Logic) | (FStar_Syntax_Syntax.Assumption) -> begin
true
end
| uu____13592 -> begin
false
end))))
in (

let constructor_or_logic_type_decl = (fun c -> (match (is_logical) with
| true -> begin
(

let uu____13615 = c
in (match (uu____13615) with
| (name, args, uu____13627, uu____13628, uu____13629) -> begin
(

let uu____13636 = (

let uu____13637 = (

let uu____13643 = (FStar_All.pipe_right args (FStar_List.map Prims.snd))
in ((name), (uu____13643), (FStar_SMTEncoding_Term.Term_sort), (None)))
in FStar_SMTEncoding_Term.DeclFun (uu____13637))
in (uu____13636)::[])
end))
end
| uu____13653 -> begin
(FStar_SMTEncoding_Term.constructor_to_decl c)
end))
in (

let inversion_axioms = (fun tapp vars -> (

let uu____13668 = (FStar_All.pipe_right datas (FStar_Util.for_some (fun l -> (

let uu____13671 = (FStar_TypeChecker_Env.try_lookup_lid env.tcenv l)
in (FStar_All.pipe_right uu____13671 FStar_Option.isNone)))))
in (match (uu____13668) with
| true -> begin
[]
end
| uu____13681 -> begin
(

let uu____13682 = (fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort)
in (match (uu____13682) with
| (xxsym, xx) -> begin
(

let uu____13688 = (FStar_All.pipe_right datas (FStar_List.fold_left (fun uu____13699 l -> (match (uu____13699) with
| (out, decls) -> begin
(

let uu____13711 = (FStar_TypeChecker_Env.lookup_datacon env.tcenv l)
in (match (uu____13711) with
| (uu____13717, data_t) -> begin
(

let uu____13719 = (FStar_Syntax_Util.arrow_formals data_t)
in (match (uu____13719) with
| (args, res) -> begin
(

let indices = (

let uu____13748 = (

let uu____13749 = (FStar_Syntax_Subst.compress res)
in uu____13749.FStar_Syntax_Syntax.n)
in (match (uu____13748) with
| FStar_Syntax_Syntax.Tm_app (uu____13757, indices) -> begin
indices
end
| uu____13773 -> begin
[]
end))
in (

let env = (FStar_All.pipe_right args (FStar_List.fold_left (fun env uu____13785 -> (match (uu____13785) with
| (x, uu____13789) -> begin
(

let uu____13790 = (

let uu____13791 = (

let uu____13795 = (mk_term_projector_name l x)
in ((uu____13795), ((xx)::[])))
in (FStar_SMTEncoding_Util.mkApp uu____13791))
in (push_term_var env x uu____13790))
end)) env))
in (

let uu____13797 = (encode_args indices env)
in (match (uu____13797) with
| (indices, decls') -> begin
((match (((FStar_List.length indices) <> (FStar_List.length vars))) with
| true -> begin
(failwith "Impossible")
end
| uu____13815 -> begin
()
end);
(

let eqs = (

let uu____13817 = (FStar_List.map2 (fun v a -> (

let uu____13825 = (

let uu____13828 = (FStar_SMTEncoding_Util.mkFreeV v)
in ((uu____13828), (a)))
in (FStar_SMTEncoding_Util.mkEq uu____13825))) vars indices)
in (FStar_All.pipe_right uu____13817 FStar_SMTEncoding_Util.mk_and_l))
in (

let uu____13830 = (

let uu____13831 = (

let uu____13834 = (

let uu____13835 = (

let uu____13838 = (mk_data_tester env l xx)
in ((uu____13838), (eqs)))
in (FStar_SMTEncoding_Util.mkAnd uu____13835))
in ((out), (uu____13834)))
in (FStar_SMTEncoding_Util.mkOr uu____13831))
in ((uu____13830), ((FStar_List.append decls decls')))));
)
end))))
end))
end))
end)) ((FStar_SMTEncoding_Util.mkFalse), ([]))))
in (match (uu____13688) with
| (data_ax, decls) -> begin
(

let uu____13846 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____13846) with
| (ffsym, ff) -> begin
(

let fuel_guarded_inversion = (

let xx_has_type_sfuel = (match (((FStar_List.length datas) > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____13857 = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((ff)::[])))
in (FStar_SMTEncoding_Term.mk_HasTypeFuel uu____13857 xx tapp))
end
| uu____13859 -> begin
(FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
end)
in (

let uu____13860 = (

let uu____13865 = (

let uu____13866 = (

let uu____13872 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____13880 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_sfuel), (data_ax)))
in ((((xx_has_type_sfuel)::[])::[]), (uu____13872), (uu____13880))))
in (FStar_SMTEncoding_Util.mkForall uu____13866))
in (

let uu____13888 = (

let uu____13890 = (varops.mk_unique (Prims.strcat "fuel_guarded_inversion_" t.FStar_Ident.str))
in Some (uu____13890))
in ((uu____13865), (Some ("inversion axiom")), (uu____13888))))
in FStar_SMTEncoding_Term.Assume (uu____13860)))
in (

let pattern_guarded_inversion = (

let uu____13895 = ((contains_name env "Prims.inversion") && ((FStar_List.length datas) > (Prims.parse_int "1")))
in (match (uu____13895) with
| true -> begin
(

let xx_has_type_fuel = (FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp)
in (

let pattern_guard = (FStar_SMTEncoding_Util.mkApp (("Prims.inversion"), ((tapp)::[])))
in (

let uu____13903 = (

let uu____13904 = (

let uu____13909 = (

let uu____13910 = (

let uu____13916 = (add_fuel ((ffsym), (FStar_SMTEncoding_Term.Fuel_sort)) ((((xxsym), (FStar_SMTEncoding_Term.Term_sort)))::vars))
in (

let uu____13924 = (FStar_SMTEncoding_Util.mkImp ((xx_has_type_fuel), (data_ax)))
in ((((xx_has_type_fuel)::(pattern_guard)::[])::[]), (uu____13916), (uu____13924))))
in (FStar_SMTEncoding_Util.mkForall uu____13910))
in (

let uu____13932 = (

let uu____13934 = (varops.mk_unique (Prims.strcat "pattern_guarded_inversion_" t.FStar_Ident.str))
in Some (uu____13934))
in ((uu____13909), (Some ("inversion axiom")), (uu____13932))))
in FStar_SMTEncoding_Term.Assume (uu____13904))
in (uu____13903)::[])))
end
| uu____13937 -> begin
[]
end))
in (FStar_List.append decls (FStar_List.append ((fuel_guarded_inversion)::[]) pattern_guarded_inversion))))
end))
end))
end))
end)))
in (

let uu____13938 = (

let uu____13946 = (

let uu____13947 = (FStar_Syntax_Subst.compress k)
in uu____13947.FStar_Syntax_Syntax.n)
in (match (uu____13946) with
| FStar_Syntax_Syntax.Tm_arrow (formals, kres) -> begin
(((FStar_List.append tps formals)), ((FStar_Syntax_Util.comp_result kres)))
end
| uu____13976 -> begin
((tps), (k))
end))
in (match (uu____13938) with
| (formals, res) -> begin
(

let uu____13991 = (FStar_Syntax_Subst.open_term formals res)
in (match (uu____13991) with
| (formals, res) -> begin
(

let uu____13998 = (encode_binders None formals env)
in (match (uu____13998) with
| (vars, guards, env', binder_decls, uu____14013) -> begin
(

let uu____14020 = (new_term_constant_and_tok_from_lid env t)
in (match (uu____14020) with
| (tname, ttok, env) -> begin
(

let ttok_tm = (FStar_SMTEncoding_Util.mkApp ((ttok), ([])))
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let tapp = (

let uu____14033 = (

let uu____14037 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in ((tname), (uu____14037)))
in (FStar_SMTEncoding_Util.mkApp uu____14033))
in (

let uu____14042 = (

let tname_decl = (

let uu____14048 = (

let uu____14057 = (FStar_All.pipe_right vars (FStar_List.map (fun uu____14069 -> (match (uu____14069) with
| (n, s) -> begin
(((Prims.strcat tname n)), (s))
end))))
in (

let uu____14076 = (varops.next_id ())
in ((tname), (uu____14057), (FStar_SMTEncoding_Term.Term_sort), (uu____14076), (false))))
in (constructor_or_logic_type_decl uu____14048))
in (

let uu____14080 = (match (vars) with
| [] -> begin
(

let uu____14087 = (

let uu____14088 = (

let uu____14090 = (FStar_SMTEncoding_Util.mkApp ((tname), ([])))
in (FStar_All.pipe_left (fun _0_38 -> Some (_0_38)) uu____14090))
in (push_free_var env t tname uu____14088))
in (([]), (uu____14087)))
end
| uu____14094 -> begin
(

let ttok_decl = FStar_SMTEncoding_Term.DeclFun (((ttok), ([]), (FStar_SMTEncoding_Term.Term_sort), (Some ("token"))))
in (

let ttok_fresh = (

let uu____14100 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ttok), (FStar_SMTEncoding_Term.Term_sort)) uu____14100))
in (

let ttok_app = (mk_Apply ttok_tm vars)
in (

let pats = ((ttok_app)::[])::((tapp)::[])::[]
in (

let name_tok_corr = (

let uu____14109 = (

let uu____14114 = (

let uu____14115 = (

let uu____14123 = (FStar_SMTEncoding_Util.mkEq ((ttok_app), (tapp)))
in ((pats), (None), (vars), (uu____14123)))
in (FStar_SMTEncoding_Util.mkForall' uu____14115))
in ((uu____14114), (Some ("name-token correspondence")), (Some ((Prims.strcat "token_correspondence_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14109))
in (((ttok_decl)::(ttok_fresh)::(name_tok_corr)::[]), (env)))))))
end)
in (match (uu____14080) with
| (tok_decls, env) -> begin
(((FStar_List.append tname_decl tok_decls)), (env))
end)))
in (match (uu____14042) with
| (decls, env) -> begin
(

let kindingAx = (

let uu____14147 = (encode_term_pred None res env' tapp)
in (match (uu____14147) with
| (k, decls) -> begin
(

let karr = (match (((FStar_List.length formals) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____14161 = (

let uu____14162 = (

let uu____14167 = (

let uu____14168 = (FStar_SMTEncoding_Term.mk_PreType ttok_tm)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____14168))
in ((uu____14167), (Some ("kinding")), (Some ((Prims.strcat "pre_kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14162))
in (uu____14161)::[])
end
| uu____14171 -> begin
[]
end)
in (

let uu____14172 = (

let uu____14174 = (

let uu____14176 = (

let uu____14177 = (

let uu____14182 = (

let uu____14183 = (

let uu____14189 = (FStar_SMTEncoding_Util.mkImp ((guard), (k)))
in ((((tapp)::[])::[]), (vars), (uu____14189)))
in (FStar_SMTEncoding_Util.mkForall uu____14183))
in ((uu____14182), (None), (Some ((Prims.strcat "kinding_" ttok)))))
in FStar_SMTEncoding_Term.Assume (uu____14177))
in (uu____14176)::[])
in (FStar_List.append karr uu____14174))
in (FStar_List.append decls uu____14172)))
end))
in (

let aux = (

let uu____14199 = (

let uu____14201 = (inversion_axioms tapp vars)
in (

let uu____14203 = (

let uu____14205 = (pretype_axiom tapp vars)
in (uu____14205)::[])
in (FStar_List.append uu____14201 uu____14203)))
in (FStar_List.append kindingAx uu____14199))
in (

let g = (FStar_List.append decls (FStar_List.append binder_decls aux))
in ((g), (env)))))
end)))))
end))
end))
end))
end)))))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14210, uu____14211, uu____14212, uu____14213, uu____14214, uu____14215, uu____14216) when (FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid) -> begin
(([]), (env))
end
| FStar_Syntax_Syntax.Sig_datacon (d, uu____14223, t, uu____14225, n_tps, quals, uu____14228, drange) -> begin
(

let uu____14234 = (new_term_constant_and_tok_from_lid env d)
in (match (uu____14234) with
| (ddconstrsym, ddtok, env) -> begin
(

let ddtok_tm = (FStar_SMTEncoding_Util.mkApp ((ddtok), ([])))
in (

let uu____14245 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____14245) with
| (formals, t_res) -> begin
(

let uu____14267 = (fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____14267) with
| (fuel_var, fuel_tm) -> begin
(

let s_fuel_tm = (FStar_SMTEncoding_Util.mkApp (("SFuel"), ((fuel_tm)::[])))
in (

let uu____14276 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____14276) with
| (vars, guards, env', binder_decls, names) -> begin
(

let projectors = (FStar_All.pipe_right names (FStar_List.map (fun x -> (

let uu____14309 = (mk_term_projector_name d x)
in ((uu____14309), (FStar_SMTEncoding_Term.Term_sort))))))
in (

let datacons = (

let uu____14311 = (

let uu____14320 = (varops.next_id ())
in ((ddconstrsym), (projectors), (FStar_SMTEncoding_Term.Term_sort), (uu____14320), (true)))
in (FStar_All.pipe_right uu____14311 FStar_SMTEncoding_Term.constructor_to_decl))
in (

let app = (mk_Apply ddtok_tm vars)
in (

let guard = (FStar_SMTEncoding_Util.mk_and_l guards)
in (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars)
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (

let uu____14340 = (encode_term_pred None t env ddtok_tm)
in (match (uu____14340) with
| (tok_typing, decls3) -> begin
(

let uu____14347 = (encode_binders (Some (fuel_tm)) formals env)
in (match (uu____14347) with
| (vars', guards', env'', decls_formals, uu____14362) -> begin
(

let uu____14369 = (

let xvars = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars')
in (

let dapp = (FStar_SMTEncoding_Util.mkApp ((ddconstrsym), (xvars)))
in (encode_term_pred (Some (fuel_tm)) t_res env'' dapp)))
in (match (uu____14369) with
| (ty_pred', decls_pred) -> begin
(

let guard' = (FStar_SMTEncoding_Util.mk_and_l guards')
in (

let proxy_fresh = (match (formals) with
| [] -> begin
[]
end
| uu____14388 -> begin
(

let uu____14392 = (

let uu____14393 = (varops.next_id ())
in (FStar_SMTEncoding_Term.fresh_token ((ddtok), (FStar_SMTEncoding_Term.Term_sort)) uu____14393))
in (uu____14392)::[])
end)
in (

let encode_elim = (fun uu____14400 -> (

let uu____14401 = (FStar_Syntax_Util.head_and_args t_res)
in (match (uu____14401) with
| (head, args) -> begin
(

let uu____14430 = (

let uu____14431 = (FStar_Syntax_Subst.compress head)
in uu____14431.FStar_Syntax_Syntax.n)
in (match (uu____14430) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _)) | (FStar_Syntax_Syntax.Tm_fvar (fv)) -> begin
(

let encoded_head = (lookup_free_var_name env' fv.FStar_Syntax_Syntax.fv_name)
in (

let uu____14449 = (encode_args args env')
in (match (uu____14449) with
| (encoded_args, arg_decls) -> begin
(

let uu____14460 = (FStar_List.fold_left (fun uu____14471 arg -> (match (uu____14471) with
| (env, arg_vars, eqns) -> begin
(

let uu____14490 = (

let uu____14494 = (FStar_Syntax_Syntax.new_bv None FStar_Syntax_Syntax.tun)
in (gen_term_var env uu____14494))
in (match (uu____14490) with
| (uu____14500, xv, env) -> begin
(

let uu____14503 = (

let uu____14505 = (FStar_SMTEncoding_Util.mkEq ((arg), (xv)))
in (uu____14505)::eqns)
in ((env), ((xv)::arg_vars), (uu____14503)))
end))
end)) ((env'), ([]), ([])) encoded_args)
in (match (uu____14460) with
| (uu____14513, arg_vars, eqns) -> begin
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

let uu____14534 = (

let uu____14539 = (

let uu____14540 = (

let uu____14546 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14552 = (

let uu____14553 = (

let uu____14556 = (FStar_SMTEncoding_Util.mk_and_l (FStar_List.append eqns guards))
in ((ty_pred), (uu____14556)))
in (FStar_SMTEncoding_Util.mkImp uu____14553))
in ((((ty_pred)::[])::[]), (uu____14546), (uu____14552))))
in (FStar_SMTEncoding_Util.mkForall uu____14540))
in ((uu____14539), (Some ("data constructor typing elim")), (Some ((Prims.strcat "data_elim_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (uu____14534))
in (

let subterm_ordering = (match ((FStar_Ident.lid_equals d FStar_Syntax_Const.lextop_lid)) with
| true -> begin
(

let x = (

let uu____14570 = (varops.fresh "x")
in ((uu____14570), (FStar_SMTEncoding_Term.Term_sort)))
in (

let xtm = (FStar_SMTEncoding_Util.mkFreeV x)
in (

let uu____14572 = (

let uu____14577 = (

let uu____14578 = (

let uu____14584 = (

let uu____14587 = (

let uu____14589 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in (uu____14589)::[])
in (uu____14587)::[])
in (

let uu____14592 = (

let uu____14593 = (

let uu____14596 = (FStar_SMTEncoding_Term.mk_tester "LexCons" xtm)
in (

let uu____14597 = (FStar_SMTEncoding_Util.mk_Precedes xtm dapp)
in ((uu____14596), (uu____14597))))
in (FStar_SMTEncoding_Util.mkImp uu____14593))
in ((uu____14584), ((x)::[]), (uu____14592))))
in (FStar_SMTEncoding_Util.mkForall uu____14578))
in (

let uu____14607 = (

let uu____14609 = (varops.mk_unique "lextop")
in Some (uu____14609))
in ((uu____14577), (Some ("lextop is top")), (uu____14607))))
in FStar_SMTEncoding_Term.Assume (uu____14572))))
end
| uu____14612 -> begin
(

let prec = (FStar_All.pipe_right vars (FStar_List.collect (fun v -> (match ((Prims.snd v)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
[]
end
| FStar_SMTEncoding_Term.Term_sort -> begin
(

let uu____14623 = (

let uu____14624 = (FStar_SMTEncoding_Util.mkFreeV v)
in (FStar_SMTEncoding_Util.mk_Precedes uu____14624 dapp))
in (uu____14623)::[])
end
| uu____14625 -> begin
(failwith "unexpected sort")
end))))
in (

let uu____14627 = (

let uu____14632 = (

let uu____14633 = (

let uu____14639 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) (FStar_List.append vars arg_binders))
in (

let uu____14645 = (

let uu____14646 = (

let uu____14649 = (FStar_SMTEncoding_Util.mk_and_l prec)
in ((ty_pred), (uu____14649)))
in (FStar_SMTEncoding_Util.mkImp uu____14646))
in ((((ty_pred)::[])::[]), (uu____14639), (uu____14645))))
in (FStar_SMTEncoding_Util.mkForall uu____14633))
in ((uu____14632), (Some ("subterm ordering")), (Some ((Prims.strcat "subterm_ordering_" ddconstrsym)))))
in FStar_SMTEncoding_Term.Assume (uu____14627)))
end)
in ((arg_decls), ((typing_inversion)::(subterm_ordering)::[]))))))))))
end))
end)))
end
| uu____14660 -> begin
((

let uu____14662 = (

let uu____14663 = (FStar_Syntax_Print.lid_to_string d)
in (

let uu____14664 = (FStar_Syntax_Print.term_to_string head)
in (FStar_Util.format2 "Constructor %s builds an unexpected type %s\n" uu____14663 uu____14664)))
in (FStar_Errors.warn drange uu____14662));
(([]), ([]));
)
end))
end)))
in (

let uu____14667 = (encode_elim ())
in (match (uu____14667) with
| (decls2, elim) -> begin
(

let g = (

let uu____14679 = (

let uu____14681 = (

let uu____14683 = (

let uu____14685 = (

let uu____14687 = (

let uu____14688 = (

let uu____14694 = (

let uu____14696 = (

let uu____14697 = (FStar_Syntax_Print.lid_to_string d)
in (FStar_Util.format1 "data constructor proxy: %s" uu____14697))
in Some (uu____14696))
in ((ddtok), ([]), (FStar_SMTEncoding_Term.Term_sort), (uu____14694)))
in FStar_SMTEncoding_Term.DeclFun (uu____14688))
in (uu____14687)::[])
in (

let uu____14700 = (

let uu____14702 = (

let uu____14704 = (

let uu____14706 = (

let uu____14708 = (

let uu____14710 = (

let uu____14712 = (

let uu____14713 = (

let uu____14718 = (

let uu____14719 = (

let uu____14725 = (FStar_SMTEncoding_Util.mkEq ((app), (dapp)))
in ((((app)::[])::[]), (vars), (uu____14725)))
in (FStar_SMTEncoding_Util.mkForall uu____14719))
in ((uu____14718), (Some ("equality for proxy")), (Some ((Prims.strcat "equality_tok_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (uu____14713))
in (

let uu____14733 = (

let uu____14735 = (

let uu____14736 = (

let uu____14741 = (

let uu____14742 = (

let uu____14748 = (add_fuel ((fuel_var), (FStar_SMTEncoding_Term.Fuel_sort)) vars')
in (

let uu____14754 = (FStar_SMTEncoding_Util.mkImp ((guard'), (ty_pred')))
in ((((ty_pred')::[])::[]), (uu____14748), (uu____14754))))
in (FStar_SMTEncoding_Util.mkForall uu____14742))
in ((uu____14741), (Some ("data constructor typing intro")), (Some ((Prims.strcat "data_typing_intro_" ddtok)))))
in FStar_SMTEncoding_Term.Assume (uu____14736))
in (uu____14735)::[])
in (uu____14712)::uu____14733))
in (FStar_SMTEncoding_Term.Assume (((tok_typing), (Some ("typing for data constructor proxy")), (Some ((Prims.strcat "typing_tok_" ddtok))))))::uu____14710)
in (FStar_List.append uu____14708 elim))
in (FStar_List.append decls_pred uu____14706))
in (FStar_List.append decls_formals uu____14704))
in (FStar_List.append proxy_fresh uu____14702))
in (FStar_List.append uu____14685 uu____14700)))
in (FStar_List.append decls3 uu____14683))
in (FStar_List.append decls2 uu____14681))
in (FStar_List.append binder_decls uu____14679))
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
and encode_signature : env_t  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * env_t) = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.fold_left (fun uu____14777 se -> (match (uu____14777) with
| (g, env) -> begin
(

let uu____14789 = (encode_sigelt env se)
in (match (uu____14789) with
| (g', env) -> begin
(((FStar_List.append g g')), (env))
end))
end)) (([]), (env)))))


let encode_env_bindings : env_t  ->  FStar_TypeChecker_Env.binding Prims.list  ->  (FStar_SMTEncoding_Term.decls_t * env_t) = (fun env bindings -> (

let encode_binding = (fun b uu____14825 -> (match (uu____14825) with
| (i, decls, env) -> begin
(match (b) with
| FStar_TypeChecker_Env.Binding_univ (uu____14843) -> begin
(((i + (Prims.parse_int "1"))), ([]), (env))
end
| FStar_TypeChecker_Env.Binding_var (x) -> begin
(

let t1 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in ((

let uu____14848 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____14848) with
| true -> begin
(

let uu____14849 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14850 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14851 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3 "Normalized %s : %s to %s\n" uu____14849 uu____14850 uu____14851))))
end
| uu____14852 -> begin
()
end));
(

let uu____14853 = (encode_term t1 env)
in (match (uu____14853) with
| (t, decls') -> begin
(

let t_hash = (FStar_SMTEncoding_Term.hash_of_term t)
in (

let uu____14863 = (

let uu____14867 = (

let uu____14868 = (

let uu____14869 = (FStar_Util.digest_of_string t_hash)
in (

let uu____14870 = (

let uu____14871 = (FStar_Util.string_of_int i)
in (Prims.strcat "_" uu____14871))
in (Prims.strcat uu____14869 uu____14870)))
in (Prims.strcat "x_" uu____14868))
in (new_term_constant_from_string env x uu____14867))
in (match (uu____14863) with
| (xxsym, xx, env') -> begin
(

let t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel None xx t)
in (

let caption = (

let uu____14882 = (FStar_Options.log_queries ())
in (match (uu____14882) with
| true -> begin
(

let uu____14884 = (

let uu____14885 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____14886 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____14887 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "%s : %s (%s)" uu____14885 uu____14886 uu____14887))))
in Some (uu____14884))
end
| uu____14888 -> begin
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
| FStar_TypeChecker_Env.Binding_lid (x, (uu____14900, t)) -> begin
(

let t_norm = (whnf env t)
in (

let fv = (FStar_Syntax_Syntax.lid_as_fv x FStar_Syntax_Syntax.Delta_constant None)
in (

let uu____14909 = (encode_free_var env fv t t_norm [])
in (match (uu____14909) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))))
end
| (FStar_TypeChecker_Env.Binding_sig_inst (_, se, _)) | (FStar_TypeChecker_Env.Binding_sig (_, se)) -> begin
(

let uu____14928 = (encode_sigelt env se)
in (match (uu____14928) with
| (g, env') -> begin
(((i + (Prims.parse_int "1"))), ((FStar_List.append decls g)), (env'))
end))
end)
end))
in (

let uu____14938 = (FStar_List.fold_right encode_binding bindings (((Prims.parse_int "0")), ([]), (env)))
in (match (uu____14938) with
| (uu____14950, decls, env) -> begin
((decls), (env))
end))))


let encode_labels = (fun labs -> (

let prefix = (FStar_All.pipe_right labs (FStar_List.map (fun uu____14995 -> (match (uu____14995) with
| (l, uu____15002, uu____15003) -> begin
FStar_SMTEncoding_Term.DeclFun ((((Prims.fst l)), ([]), (FStar_SMTEncoding_Term.Bool_sort), (None)))
end))))
in (

let suffix = (FStar_All.pipe_right labs (FStar_List.collect (fun uu____15024 -> (match (uu____15024) with
| (l, uu____15032, uu____15033) -> begin
(

let uu____15038 = (FStar_All.pipe_left (fun _0_39 -> FStar_SMTEncoding_Term.Echo (_0_39)) (Prims.fst l))
in (

let uu____15039 = (

let uu____15041 = (

let uu____15042 = (FStar_SMTEncoding_Util.mkFreeV l)
in FStar_SMTEncoding_Term.Eval (uu____15042))
in (uu____15041)::[])
in (uu____15038)::uu____15039))
end))))
in ((prefix), (suffix)))))


let last_env : env_t Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let init_env : FStar_TypeChecker_Env.env  ->  Prims.unit = (fun tcenv -> (

let uu____15053 = (

let uu____15055 = (

let uu____15056 = (FStar_Util.smap_create (Prims.parse_int "100"))
in {bindings = []; depth = (Prims.parse_int "0"); tcenv = tcenv; warn = true; cache = uu____15056; nolabels = false; use_zfuel_name = false; encode_non_total_function_typ = true})
in (uu____15055)::[])
in (FStar_ST.write last_env uu____15053)))


let get_env : FStar_TypeChecker_Env.env  ->  env_t = (fun tcenv -> (

let uu____15074 = (FStar_ST.read last_env)
in (match (uu____15074) with
| [] -> begin
(failwith "No env; call init first!")
end
| (e)::uu____15080 -> begin
(

let uu___157_15082 = e
in {bindings = uu___157_15082.bindings; depth = uu___157_15082.depth; tcenv = tcenv; warn = uu___157_15082.warn; cache = uu___157_15082.cache; nolabels = uu___157_15082.nolabels; use_zfuel_name = uu___157_15082.use_zfuel_name; encode_non_total_function_typ = uu___157_15082.encode_non_total_function_typ})
end)))


let set_env : env_t  ->  Prims.unit = (fun env -> (

let uu____15086 = (FStar_ST.read last_env)
in (match (uu____15086) with
| [] -> begin
(failwith "Empty env stack")
end
| (uu____15091)::tl -> begin
(FStar_ST.write last_env ((env)::tl))
end)))


let push_env : Prims.unit  ->  Prims.unit = (fun uu____15099 -> (

let uu____15100 = (FStar_ST.read last_env)
in (match (uu____15100) with
| [] -> begin
(failwith "Empty env stack")
end
| (hd)::tl -> begin
(

let refs = (FStar_Util.smap_copy hd.cache)
in (

let top = (

let uu___158_15121 = hd
in {bindings = uu___158_15121.bindings; depth = uu___158_15121.depth; tcenv = uu___158_15121.tcenv; warn = uu___158_15121.warn; cache = refs; nolabels = uu___158_15121.nolabels; use_zfuel_name = uu___158_15121.use_zfuel_name; encode_non_total_function_typ = uu___158_15121.encode_non_total_function_typ})
in (FStar_ST.write last_env ((top)::(hd)::tl))))
end)))


let pop_env : Prims.unit  ->  Prims.unit = (fun uu____15127 -> (

let uu____15128 = (FStar_ST.read last_env)
in (match (uu____15128) with
| [] -> begin
(failwith "Popping an empty stack")
end
| (uu____15133)::tl -> begin
(FStar_ST.write last_env tl)
end)))


let mark_env : Prims.unit  ->  Prims.unit = (fun uu____15141 -> (push_env ()))


let reset_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15144 -> (pop_env ()))


let commit_mark_env : Prims.unit  ->  Prims.unit = (fun uu____15147 -> (

let uu____15148 = (FStar_ST.read last_env)
in (match (uu____15148) with
| (hd)::(uu____15154)::tl -> begin
(FStar_ST.write last_env ((hd)::tl))
end
| uu____15160 -> begin
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

let uu____15205 = (FStar_Options.log_queries ())
in (match (uu____15205) with
| true -> begin
(

let uu____15207 = (

let uu____15208 = (

let uu____15209 = (

let uu____15210 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_List.map FStar_Syntax_Print.lid_to_string))
in (FStar_All.pipe_right uu____15210 (FStar_String.concat ", ")))
in (Prims.strcat "encoding sigelt " uu____15209))
in FStar_SMTEncoding_Term.Caption (uu____15208))
in (uu____15207)::decls)
end
| uu____15215 -> begin
decls
end)))
in (

let env = (get_env tcenv)
in (

let uu____15217 = (encode_sigelt env se)
in (match (uu____15217) with
| (decls, env) -> begin
((set_env env);
(

let uu____15223 = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 uu____15223));
)
end)))))


let encode_modul : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun tcenv modul -> (

let name = (FStar_Util.format2 "%s %s" (match (modul.FStar_Syntax_Syntax.is_interface) with
| true -> begin
"interface"
end
| uu____15232 -> begin
"module"
end) modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in ((

let uu____15234 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15234) with
| true -> begin
(

let uu____15235 = (FStar_All.pipe_right (FStar_List.length modul.FStar_Syntax_Syntax.exports) FStar_Util.string_of_int)
in (FStar_Util.print2 "+++++++++++Encoding externals for %s ... %s exports\n" name uu____15235))
end
| uu____15238 -> begin
()
end));
(

let env = (get_env tcenv)
in (

let uu____15240 = (encode_signature (

let uu___159_15244 = env
in {bindings = uu___159_15244.bindings; depth = uu___159_15244.depth; tcenv = uu___159_15244.tcenv; warn = false; cache = uu___159_15244.cache; nolabels = uu___159_15244.nolabels; use_zfuel_name = uu___159_15244.use_zfuel_name; encode_non_total_function_typ = uu___159_15244.encode_non_total_function_typ}) modul.FStar_Syntax_Syntax.exports)
in (match (uu____15240) with
| (decls, env) -> begin
(

let caption = (fun decls -> (

let uu____15256 = (FStar_Options.log_queries ())
in (match (uu____15256) with
| true -> begin
(

let msg = (Prims.strcat "Externals for " name)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::decls) ((FStar_SMTEncoding_Term.Caption ((Prims.strcat "End " msg)))::[])))
end
| uu____15259 -> begin
decls
end)))
in ((set_env (

let uu___160_15261 = env
in {bindings = uu___160_15261.bindings; depth = uu___160_15261.depth; tcenv = uu___160_15261.tcenv; warn = true; cache = uu___160_15261.cache; nolabels = uu___160_15261.nolabels; use_zfuel_name = uu___160_15261.use_zfuel_name; encode_non_total_function_typ = uu___160_15261.encode_non_total_function_typ}));
(

let uu____15263 = (FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
in (match (uu____15263) with
| true -> begin
(FStar_Util.print1 "Done encoding externals for %s\n" name)
end
| uu____15264 -> begin
()
end));
(

let decls = (caption decls)
in (FStar_SMTEncoding_Z3.giveZ3 decls));
))
end)));
)))


let encode_query : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  (FStar_SMTEncoding_Term.decl Prims.list * FStar_SMTEncoding_ErrorReporting.label Prims.list * FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl Prims.list) = (fun use_env_msg tcenv q -> ((

let uu____15298 = (

let uu____15299 = (FStar_TypeChecker_Env.current_module tcenv)
in uu____15299.FStar_Ident.str)
in (FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name uu____15298));
(

let env = (get_env tcenv)
in (

let bindings = (FStar_TypeChecker_Env.fold_env tcenv (fun bs b -> (b)::bs) [])
in (

let uu____15307 = (

let rec aux = (fun bindings -> (match (bindings) with
| (FStar_TypeChecker_Env.Binding_var (x))::rest -> begin
(

let uu____15328 = (aux rest)
in (match (uu____15328) with
| (out, rest) -> begin
(

let t = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Simplify)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.tcenv x.FStar_Syntax_Syntax.sort)
in (

let uu____15344 = (

let uu____15346 = (FStar_Syntax_Syntax.mk_binder (

let uu___161_15347 = x
in {FStar_Syntax_Syntax.ppname = uu___161_15347.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___161_15347.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}))
in (uu____15346)::out)
in ((uu____15344), (rest))))
end))
end
| uu____15350 -> begin
(([]), (bindings))
end))
in (

let uu____15354 = (aux bindings)
in (match (uu____15354) with
| (closing, bindings) -> begin
(

let uu____15368 = (FStar_Syntax_Util.close_forall (FStar_List.rev closing) q)
in ((uu____15368), (bindings)))
end)))
in (match (uu____15307) with
| (q, bindings) -> begin
(

let uu____15381 = (

let uu____15384 = (FStar_List.filter (fun uu___133_15386 -> (match (uu___133_15386) with
| FStar_TypeChecker_Env.Binding_sig (uu____15387) -> begin
false
end
| uu____15391 -> begin
true
end)) bindings)
in (encode_env_bindings env uu____15384))
in (match (uu____15381) with
| (env_decls, env) -> begin
((

let uu____15402 = (((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTEncoding")))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug tcenv) (FStar_Options.Other ("SMTQuery"))))
in (match (uu____15402) with
| true -> begin
(

let uu____15403 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.print1 "Encoding query formula: %s\n" uu____15403))
end
| uu____15404 -> begin
()
end));
(

let uu____15405 = (encode_formula q env)
in (match (uu____15405) with
| (phi, qdecls) -> begin
(

let uu____15417 = (

let uu____15420 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_SMTEncoding_ErrorReporting.label_goals use_env_msg uu____15420 phi))
in (match (uu____15417) with
| (labels, phi) -> begin
(

let uu____15430 = (encode_labels labels)
in (match (uu____15430) with
| (label_prefix, label_suffix) -> begin
(

let query_prelude = (FStar_List.append env_decls (FStar_List.append label_prefix qdecls))
in (

let qry = (

let uu____15451 = (

let uu____15456 = (FStar_SMTEncoding_Util.mkNot phi)
in (

let uu____15457 = (

let uu____15459 = (varops.mk_unique "@query")
in Some (uu____15459))
in ((uu____15456), (Some ("query")), (uu____15457))))
in FStar_SMTEncoding_Term.Assume (uu____15451))
in (

let suffix = (

let uu____15464 = (

let uu____15466 = (

let uu____15468 = (FStar_Options.print_z3_statistics ())
in (match (uu____15468) with
| true -> begin
(FStar_SMTEncoding_Term.PrintStats)::[]
end
| uu____15470 -> begin
[]
end))
in (FStar_List.append uu____15466 ((FStar_SMTEncoding_Term.Echo ("Done!"))::[])))
in (FStar_List.append label_suffix uu____15464))
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

let uu____15481 = (encode_formula q env)
in (match (uu____15481) with
| (f, uu____15485) -> begin
((FStar_SMTEncoding_Z3.pop "query");
(match (f.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____15487) -> begin
true
end
| uu____15490 -> begin
false
end);
)
end));
)))





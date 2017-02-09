
open Prims
exception Not_a_wp_implication of (Prims.string)


let uu___is_Not_a_wp_implication : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not_a_wp_implication (uu____6) -> begin
true
end
| uu____7 -> begin
false
end))


let __proj__Not_a_wp_implication__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Not_a_wp_implication (uu____14) -> begin
uu____14
end))


type label =
FStar_SMTEncoding_Term.error_label


type labels =
FStar_SMTEncoding_Term.error_labels


let sort_labels : (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list  ->  ((FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) * Prims.bool) Prims.list = (fun l -> (FStar_List.sortWith (fun uu____35 uu____36 -> (match (((uu____35), (uu____36))) with
| (((uu____57, uu____58, r1), uu____60), ((uu____61, uu____62, r2), uu____64)) -> begin
(FStar_Range.compare r1 r2)
end)) l))


let remove_dups : labels  ->  (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_Util.remove_dups (fun uu____91 uu____92 -> (match (((uu____91), (uu____92))) with
| ((uu____105, m1, r1), (uu____108, m2, r2)) -> begin
((r1 = r2) && (m1 = m2))
end)) l))


type msg =
(Prims.string * FStar_Range.range)


type ranges =
(Prims.string Prims.option * FStar_Range.range) Prims.list


let fresh_label : Prims.string  ->  FStar_Range.range  ->  FStar_SMTEncoding_Term.term  ->  (label * FStar_SMTEncoding_Term.term) = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun message range t -> (

let l = ((FStar_Util.incr ctr);
(

let uu____142 = (

let uu____143 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int uu____143))
in (FStar_Util.format1 "label_%s" uu____142));
)
in (

let lvar = ((l), (FStar_SMTEncoding_Term.Bool_sort))
in (

let label = ((lvar), (message), (range))
in (

let lterm = (FStar_SMTEncoding_Util.mkFreeV lvar)
in (

let lt = (FStar_SMTEncoding_Term.mkOr ((lterm), (t)) range)
in ((label), (lt)))))))))


let label_goals : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Range.range  ->  FStar_SMTEncoding_Term.term  ->  (labels * FStar_SMTEncoding_Term.term) = (fun use_env_msg r q -> (

let rec is_a_post_condition = (fun post_name_opt tm -> (match (((post_name_opt), (tm.FStar_SMTEncoding_Term.tm))) with
| (None, uu____194) -> begin
false
end
| (Some (nm), FStar_SMTEncoding_Term.FreeV (nm', uu____198)) -> begin
(nm = nm')
end
| ((_, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Valid"), (tm)::[]))) | ((_, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("ApplyTT"), (tm)::_))) -> begin
(is_a_post_condition post_name_opt tm)
end
| uu____208 -> begin
false
end))
in (

let conjuncts = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> begin
cs
end
| uu____221 -> begin
(t)::[]
end))
in (

let is_guard_free = (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____227; FStar_SMTEncoding_Term.rng = uu____228})::[])::[], iopt, uu____230, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = uu____233; FStar_SMTEncoding_Term.rng = uu____234}) -> begin
true
end
| uu____253 -> begin
false
end))
in (

let is_a_named_continuation = (fun lhs -> (FStar_All.pipe_right (conjuncts lhs) (FStar_Util.for_some is_guard_free)))
in (

let uu____259 = (match (use_env_msg) with
| None -> begin
((false), (""))
end
| Some (f) -> begin
(

let uu____271 = (f ())
in ((true), (uu____271)))
end)
in (match (uu____259) with
| (flag, msg_prefix) -> begin
(

let fresh_label = (fun msg ropt rng t -> (

let msg = (match (flag) with
| true -> begin
(Prims.strcat "Failed to verify implicit argument: " msg)
end
| uu____294 -> begin
msg
end)
in (

let rng = (match (ropt) with
| None -> begin
rng
end
| Some (r) -> begin
(

let uu___99_297 = r
in {FStar_Range.def_range = rng.FStar_Range.def_range; FStar_Range.use_range = uu___99_297.FStar_Range.use_range})
end)
in (fresh_label msg rng t))))
in (

let rec aux = (fun default_msg ropt post_name_opt labels q -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
((labels), (q))
end
| FStar_SMTEncoding_Term.LblPos (uu____329) -> begin
(failwith "Impossible")
end
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", uu____336) -> begin
(

let fallback = (fun msg -> (aux default_msg ropt post_name_opt labels arg))
in try
(match (()) with
| () -> begin
(match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, (post)::sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____360; FStar_SMTEncoding_Term.rng = rng}) -> begin
(

let post_name = (

let uu____376 = (

let uu____377 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____377))
in (Prims.strcat "^^post_condition_" uu____376))
in (

let names = (

let uu____382 = (FStar_List.mapi (fun i s -> (

let uu____390 = (

let uu____391 = (FStar_Util.string_of_int i)
in (Prims.strcat "^^" uu____391))
in ((uu____390), (s)))) sorts)
in (((post_name), (post)))::uu____382)
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names)
in (

let uu____398 = (

let uu____401 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____402 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____401), (uu____402))))
in (match (uu____398) with
| (lhs, rhs) -> begin
(

let uu____408 = (match (lhs.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, clauses_lhs) -> begin
(

let uu____418 = (FStar_Util.prefix clauses_lhs)
in (match (uu____418) with
| (req, ens) -> begin
(match (ens.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats_ens, iopt_ens, sorts_ens, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (ensures_conjuncts)::(post)::[]); FStar_SMTEncoding_Term.freevars = uu____437; FStar_SMTEncoding_Term.rng = rng_ens}) when (is_a_post_condition (Some (post_name)) post) -> begin
(

let uu____452 = (aux "could not prove post-condition" None (Some (post_name)) labels ensures_conjuncts)
in (match (uu____452) with
| (labels, ensures_conjuncts) -> begin
(

let pats_ens = (match (pats_ens) with
| ([]) | (([])::[]) -> begin
((post)::[])::[]
end
| uu____473 -> begin
pats_ens
end)
in (

let ens = (

let uu____477 = (

let uu____478 = (

let uu____488 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((ensures_conjuncts)::(post)::[])))) rng_ens)
in ((FStar_SMTEncoding_Term.Forall), (pats_ens), (iopt_ens), (sorts_ens), (uu____488)))
in FStar_SMTEncoding_Term.Quant (uu____478))
in (FStar_SMTEncoding_Term.mk uu____477 ens.FStar_SMTEncoding_Term.rng))
in (

let lhs = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.And), ((FStar_List.append req ((ens)::[])))))) lhs.FStar_SMTEncoding_Term.rng)
in (

let uu____496 = (FStar_SMTEncoding_Term.abstr names lhs)
in ((labels), (uu____496))))))
end))
end
| uu____498 -> begin
(

let uu____499 = (

let uu____500 = (

let uu____501 = (

let uu____502 = (

let uu____503 = (FStar_SMTEncoding_Term.print_smt_term ens)
in (Prims.strcat "  ... " uu____503))
in (Prims.strcat post_name uu____502))
in (Prims.strcat "Ensures clause doesn\'t match post name:  " uu____501))
in Not_a_wp_implication (uu____500))
in (Prims.raise uu____499))
end)
end))
end
| uu____507 -> begin
(

let uu____508 = (

let uu____509 = (

let uu____510 = (FStar_SMTEncoding_Term.print_smt_term lhs)
in (Prims.strcat "LHS not a conjunct: " uu____510))
in Not_a_wp_implication (uu____509))
in (Prims.raise uu____508))
end)
in (match (uu____408) with
| (labels, lhs) -> begin
(

let uu____521 = (

let uu____525 = (aux default_msg None (Some (post_name)) labels rhs)
in (match (uu____525) with
| (labels, rhs) -> begin
(

let uu____536 = (FStar_SMTEncoding_Term.abstr names rhs)
in ((labels), (uu____536)))
end))
in (match (uu____521) with
| (labels, rhs) -> begin
(

let body = (FStar_SMTEncoding_Term.mkImp ((lhs), (rhs)) rng)
in (

let uu____546 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), ((post)::sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (uu____546))))
end))
end))
end)))))
end
| uu____552 -> begin
(

let uu____553 = (

let uu____554 = (FStar_SMTEncoding_Term.print_smt_term arg)
in (Prims.strcat "arg not a quant: " uu____554))
in (fallback uu____553))
end)
end)
with
| Not_a_wp_implication (msg) -> begin
(fallback msg)
end)
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(aux reason (Some (r)) post_name_opt labels arg)
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, [], None, (post)::[], {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____566; FStar_SMTEncoding_Term.rng = rng}) when (is_a_named_continuation lhs) -> begin
(

let post_name = (

let uu____579 = (

let uu____580 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____580))
in (Prims.strcat "^^post_condition_" uu____579))
in (

let names = ((post_name), (post))
in (

let instantiation = (

let uu____586 = (FStar_SMTEncoding_Util.mkFreeV names)
in (uu____586)::[])
in (

let uu____587 = (

let uu____590 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____591 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____590), (uu____591))))
in (match (uu____587) with
| (lhs, rhs) -> begin
(

let uu____597 = (FStar_Util.fold_map (fun labels tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____610; FStar_SMTEncoding_Term.rng = uu____611})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = uu____616; FStar_SMTEncoding_Term.rng = uu____617}) -> begin
(

let uu____636 = (aux default_msg None post_name_opt labels r)
in (match (uu____636) with
| (labels, r) -> begin
(

let uu____647 = (

let uu____648 = (

let uu____649 = (

let uu____659 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Iff), ((l)::(r)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (Some ((Prims.parse_int "0"))), (sorts), (uu____659)))
in FStar_SMTEncoding_Term.Quant (uu____649))
in (FStar_SMTEncoding_Term.mk uu____648 q.FStar_SMTEncoding_Term.rng))
in ((labels), (uu____647)))
end))
end
| uu____668 -> begin
((labels), (tm))
end)) labels (conjuncts lhs))
in (match (uu____597) with
| (labels, lhs_conjs) -> begin
(

let uu____679 = (aux default_msg None (Some (post_name)) labels rhs)
in (match (uu____679) with
| (labels, rhs) -> begin
(

let body = (

let uu____691 = (

let uu____692 = (

let uu____695 = (FStar_SMTEncoding_Term.mk_and_l lhs_conjs lhs.FStar_SMTEncoding_Term.rng)
in ((uu____695), (rhs)))
in (FStar_SMTEncoding_Term.mkImp uu____692 rng))
in (FStar_All.pipe_right uu____691 (FStar_SMTEncoding_Term.abstr ((names)::[]))))
in (

let q = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), ([]), (None), ((post)::[]), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (q))))
end))
end))
end)))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let uu____710 = (aux default_msg ropt post_name_opt labels rhs)
in (match (uu____710) with
| (labels, rhs) -> begin
(

let uu____721 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs)))
in ((labels), (uu____721)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let uu____726 = (FStar_Util.fold_map (aux default_msg ropt post_name_opt) labels conjuncts)
in (match (uu____726) with
| (labels, conjuncts) -> begin
(

let uu____741 = (FStar_SMTEncoding_Term.mk_and_l conjuncts q.FStar_SMTEncoding_Term.rng)
in ((labels), (uu____741)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]) -> begin
(

let uu____747 = (aux default_msg ropt post_name_opt labels q1)
in (match (uu____747) with
| (labels, q1) -> begin
(

let uu____758 = (aux default_msg ropt post_name_opt labels q2)
in (match (uu____758) with
| (labels, q2) -> begin
(

let uu____769 = (FStar_SMTEncoding_Term.mkITE ((hd), (q1), (q2)) q.FStar_SMTEncoding_Term.rng)
in ((labels), (uu____769)))
end))
end))
end
| (FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, _, _, _, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, _)) -> begin
(

let uu____783 = (fresh_label default_msg ropt q.FStar_SMTEncoding_Term.rng q)
in (match (uu____783) with
| (lab, q) -> begin
(((lab)::labels), (q))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____792), uu____793) when (is_a_post_condition post_name_opt q) -> begin
((labels), (q))
end
| (FStar_SMTEncoding_Term.FreeV (_)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (_), _)) -> begin
(

let uu____817 = (fresh_label default_msg ropt q.FStar_SMTEncoding_Term.rng q)
in (match (uu____817) with
| (lab, q) -> begin
(((lab)::labels), (q))
end))
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Add, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Sub, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Div, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mul, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Minus, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mod, _)) -> begin
(failwith "Impossible: non-propositional term")
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, _)) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body) -> begin
(

let uu____860 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____860) with
| (labels, body) -> begin
(

let uu____871 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (uu____871)))
end))
end
| FStar_SMTEncoding_Term.Let (es, body) -> begin
(

let uu____881 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____881) with
| (labels, body) -> begin
(

let uu____892 = (FStar_SMTEncoding_Term.mkLet ((es), (body)) q.FStar_SMTEncoding_Term.rng)
in ((labels), (uu____892)))
end))
end))
in (aux "assertion failed" None None [] q)))
end)))))))


let detail_errors : FStar_TypeChecker_Env.env  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  ((FStar_SMTEncoding_Z3.unsat_core, (labels * FStar_SMTEncoding_Z3.error_kind)) FStar_Util.either * Prims.int))  ->  labels = (fun env all_labels askZ3 -> (

let print_banner = (fun uu____924 -> (

let uu____925 = (

let uu____926 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____926))
in (

let uu____927 = (FStar_Util.string_of_int (Prims.parse_int "5"))
in (

let uu____928 = (FStar_Util.string_of_int (FStar_List.length all_labels))
in (FStar_Util.print3_error "Detailed error report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n" uu____925 uu____927 uu____928)))))
in (

let print_result = (fun uu____940 -> (match (uu____940) with
| ((uu____946, msg, r), success) -> begin
(match (success) with
| true -> begin
(

let uu____953 = (FStar_Range.string_of_range r)
in (FStar_Util.print1_error "OK: proof obligation at %s was proven\n" uu____953))
end
| uu____954 -> begin
(FStar_Errors.report r msg)
end)
end))
in (

let elim = (fun labs -> (FStar_All.pipe_right labs (FStar_List.map (fun uu____984 -> (match (uu____984) with
| (l, uu____991, uu____992) -> begin
(

let uu____997 = (

let uu____1002 = (

let uu____1003 = (

let uu____1006 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((uu____1006), (FStar_SMTEncoding_Util.mkTrue)))
in (FStar_SMTEncoding_Util.mkEq uu____1003))
in ((uu____1002), (Some ("Disabling label")), (Some ((Prims.strcat "disable_label_" (Prims.fst l))))))
in FStar_SMTEncoding_Term.Assume (uu____997))
end)))))
in (

let rec linear_check = (fun eliminated errors active -> (match (active) with
| [] -> begin
(

let results = (

let uu____1041 = (FStar_List.map (fun x -> ((x), (true))) eliminated)
in (

let uu____1048 = (FStar_List.map (fun x -> ((x), (false))) errors)
in (FStar_List.append uu____1041 uu____1048)))
in (sort_labels results))
end
| (hd)::tl -> begin
((

let uu____1061 = (FStar_Util.string_of_int (FStar_List.length active))
in (FStar_Util.print1 "%s, " uu____1061));
(FStar_SMTEncoding_Z3.refresh ());
(

let uu____1066 = (

let uu____1073 = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl)))
in (askZ3 uu____1073))
in (match (uu____1066) with
| (result, uu____1088) -> begin
(

let uu____1097 = (FStar_Util.is_left result)
in (match (uu____1097) with
| true -> begin
(linear_check ((hd)::eliminated) errors tl)
end
| uu____1106 -> begin
(linear_check eliminated ((hd)::errors) tl)
end))
end));
)
end))
in ((print_banner ());
(FStar_Options.set_option "z3rlimit" (FStar_Options.Int ((Prims.parse_int "5"))));
(

let res = (linear_check [] [] all_labels)
in ((FStar_Util.print_string "\n");
(FStar_All.pipe_right res (FStar_List.iter print_result));
[];
));
))))))






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

let l = (FStar_Util.incr ctr);
(let _0_568 = (FStar_Util.string_of_int (FStar_ST.read ctr))
in (FStar_Util.format1 "label_%s" _0_568));

in (

let lvar = ((l), (FStar_SMTEncoding_Term.Bool_sort))
in (

let label = ((lvar), (message), (range))
in (

let lterm = (FStar_SMTEncoding_Util.mkFreeV lvar)
in (

let lt = (FStar_SMTEncoding_Term.mkOr ((lterm), (t)) range)
in ((label), (lt)))))))))


let label_goals = (fun use_env_msg r q -> (

let rec is_a_post_condition = (fun post_name_opt tm -> (match (((post_name_opt), (tm.FStar_SMTEncoding_Term.tm))) with
| (None, uu____198) -> begin
false
end
| (Some (nm), FStar_SMTEncoding_Term.FreeV (nm', uu____202)) -> begin
(nm = nm')
end
| ((_, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Valid"), (tm)::[]))) | ((_, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("ApplyTT"), (tm)::_))) -> begin
(is_a_post_condition post_name_opt tm)
end
| uu____212 -> begin
false
end))
in (

let conjuncts = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> begin
cs
end
| uu____225 -> begin
(t)::[]
end))
in (

let is_guard_free = (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____231; FStar_SMTEncoding_Term.rng = uu____232})::[])::[], iopt, uu____234, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = uu____237; FStar_SMTEncoding_Term.rng = uu____238}) -> begin
true
end
| uu____257 -> begin
false
end))
in (

let is_a_named_continuation = (fun lhs -> (FStar_All.pipe_right (conjuncts lhs) (FStar_Util.for_some is_guard_free)))
in (

let uu____263 = (match (use_env_msg) with
| None -> begin
((false), (""))
end
| Some (f) -> begin
(let _0_569 = (f ())
in ((true), (_0_569)))
end)
in (match (uu____263) with
| (flag, msg_prefix) -> begin
(

let fresh_label = (fun msg ropt rng t -> (

let msg = (match (flag) with
| true -> begin
(Prims.strcat "Failed to verify implicit argument: " msg)
end
| uu____297 -> begin
msg
end)
in (

let rng = (match (ropt) with
| None -> begin
rng
end
| Some (r) -> begin
(

let uu___141_300 = r
in {FStar_Range.def_range = rng.FStar_Range.def_range; FStar_Range.use_range = uu___141_300.FStar_Range.use_range})
end)
in (fresh_label msg rng t))))
in (

let rec aux = (fun default_msg ropt post_name_opt labels q -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
((labels), (q))
end
| FStar_SMTEncoding_Term.LblPos (uu____332) -> begin
(failwith "Impossible")
end
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", uu____339) -> begin
(

let fallback = (fun msg -> (aux default_msg ropt post_name_opt labels arg))
in try
(match (()) with
| () -> begin
(match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, (post)::sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____363; FStar_SMTEncoding_Term.rng = rng}) -> begin
(

let post_name = (let _0_571 = (let _0_570 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _0_570))
in (Prims.strcat "^^post_condition_" _0_571))
in (

let names = (let _0_574 = (FStar_List.mapi (fun i s -> (let _0_573 = (let _0_572 = (FStar_Util.string_of_int i)
in (Prims.strcat "^^" _0_572))
in ((_0_573), (s)))) sorts)
in (((post_name), (post)))::_0_574)
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names)
in (

let uu____393 = (let _0_576 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (let _0_575 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((_0_576), (_0_575))))
in (match (uu____393) with
| (lhs, rhs) -> begin
(

let uu____401 = (match (lhs.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, clauses_lhs) -> begin
(

let uu____411 = (FStar_Util.prefix clauses_lhs)
in (match (uu____411) with
| (req, ens) -> begin
(match (ens.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats_ens, iopt_ens, sorts_ens, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (ensures_conjuncts)::(post)::[]); FStar_SMTEncoding_Term.freevars = uu____430; FStar_SMTEncoding_Term.rng = rng_ens}) when (is_a_post_condition (Some (post_name)) post) -> begin
(

let uu____445 = (aux "could not prove post-condition" None (Some (post_name)) labels ensures_conjuncts)
in (match (uu____445) with
| (labels, ensures_conjuncts) -> begin
(

let pats_ens = (match (pats_ens) with
| ([]) | (([])::[]) -> begin
((post)::[])::[]
end
| uu____466 -> begin
pats_ens
end)
in (

let ens = (let _0_578 = FStar_SMTEncoding_Term.Quant ((let _0_577 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((ensures_conjuncts)::(post)::[])))) rng_ens)
in ((FStar_SMTEncoding_Term.Forall), (pats_ens), (iopt_ens), (sorts_ens), (_0_577))))
in (FStar_SMTEncoding_Term.mk _0_578 ens.FStar_SMTEncoding_Term.rng))
in (

let lhs = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.And), ((FStar_List.append req ((ens)::[])))))) lhs.FStar_SMTEncoding_Term.rng)
in (let _0_579 = (FStar_SMTEncoding_Term.abstr names lhs)
in ((labels), (_0_579))))))
end))
end
| uu____478 -> begin
(Prims.raise (Not_a_wp_implication ((let _0_582 = (let _0_581 = (let _0_580 = (FStar_SMTEncoding_Term.print_smt_term ens)
in (Prims.strcat "  ... " _0_580))
in (Prims.strcat post_name _0_581))
in (Prims.strcat "Ensures clause doesn\'t match post name:  " _0_582)))))
end)
end))
end
| uu____482 -> begin
(Prims.raise (Not_a_wp_implication ((let _0_583 = (FStar_SMTEncoding_Term.print_smt_term lhs)
in (Prims.strcat "LHS not a conjunct: " _0_583)))))
end)
in (match (uu____401) with
| (labels, lhs) -> begin
(

let uu____493 = (

let uu____497 = (aux default_msg None (Some (post_name)) labels rhs)
in (match (uu____497) with
| (labels, rhs) -> begin
(let _0_584 = (FStar_SMTEncoding_Term.abstr names rhs)
in ((labels), (_0_584)))
end))
in (match (uu____493) with
| (labels, rhs) -> begin
(

let body = (FStar_SMTEncoding_Term.mkImp ((lhs), (rhs)) rng)
in (let _0_585 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), ((post)::sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_0_585))))
end))
end))
end)))))
end
| uu____522 -> begin
(fallback (let _0_586 = (FStar_SMTEncoding_Term.print_smt_term arg)
in (Prims.strcat "arg not a quant: " _0_586)))
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
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, [], None, (post)::[], {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____534; FStar_SMTEncoding_Term.rng = rng}) when (is_a_named_continuation lhs) -> begin
(

let post_name = (let _0_588 = (let _0_587 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _0_587))
in (Prims.strcat "^^post_condition_" _0_588))
in (

let names = ((post_name), (post))
in (

let instantiation = (let _0_589 = (FStar_SMTEncoding_Util.mkFreeV names)
in (_0_589)::[])
in (

let uu____552 = (let _0_591 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (let _0_590 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((_0_591), (_0_590))))
in (match (uu____552) with
| (lhs, rhs) -> begin
(

let uu____560 = (FStar_Util.fold_map (fun labels tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____573; FStar_SMTEncoding_Term.rng = uu____574})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = uu____579; FStar_SMTEncoding_Term.rng = uu____580}) -> begin
(

let uu____599 = (aux default_msg None post_name_opt labels r)
in (match (uu____599) with
| (labels, r) -> begin
(let _0_594 = (let _0_593 = FStar_SMTEncoding_Term.Quant ((let _0_592 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Iff), ((l)::(r)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (Some ((Prims.parse_int "0"))), (sorts), (_0_592))))
in (FStar_SMTEncoding_Term.mk _0_593 q.FStar_SMTEncoding_Term.rng))
in ((labels), (_0_594)))
end))
end
| uu____618 -> begin
((labels), (tm))
end)) labels (conjuncts lhs))
in (match (uu____560) with
| (labels, lhs_conjs) -> begin
(

let uu____629 = (aux default_msg None (Some (post_name)) labels rhs)
in (match (uu____629) with
| (labels, rhs) -> begin
(

let body = (let _0_597 = (let _0_596 = (let _0_595 = (FStar_SMTEncoding_Term.mk_and_l lhs_conjs lhs.FStar_SMTEncoding_Term.rng)
in ((_0_595), (rhs)))
in (FStar_SMTEncoding_Term.mkImp _0_596 rng))
in (FStar_All.pipe_right _0_597 (FStar_SMTEncoding_Term.abstr ((names)::[]))))
in (

let q = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), ([]), (None), ((post)::[]), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (q))))
end))
end))
end)))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let uu____655 = (aux default_msg ropt post_name_opt labels rhs)
in (match (uu____655) with
| (labels, rhs) -> begin
(let _0_598 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs)))
in ((labels), (_0_598)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let uu____670 = (FStar_Util.fold_map (aux default_msg ropt post_name_opt) labels conjuncts)
in (match (uu____670) with
| (labels, conjuncts) -> begin
(let _0_599 = (FStar_SMTEncoding_Term.mk_and_l conjuncts q.FStar_SMTEncoding_Term.rng)
in ((labels), (_0_599)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]) -> begin
(

let uu____690 = (aux default_msg ropt post_name_opt labels q1)
in (match (uu____690) with
| (labels, q1) -> begin
(

let uu____701 = (aux default_msg ropt post_name_opt labels q2)
in (match (uu____701) with
| (labels, q2) -> begin
(let _0_600 = (FStar_SMTEncoding_Term.mkITE ((hd), (q1), (q2)) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_0_600)))
end))
end))
end
| (FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, _, _, _, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, _)) -> begin
(

let uu____725 = (fresh_label default_msg ropt q.FStar_SMTEncoding_Term.rng q)
in (match (uu____725) with
| (lab, q) -> begin
(((lab)::labels), (q))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____734), uu____735) when (is_a_post_condition post_name_opt q) -> begin
((labels), (q))
end
| (FStar_SMTEncoding_Term.FreeV (_)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (_), _)) -> begin
(

let uu____759 = (fresh_label default_msg ropt q.FStar_SMTEncoding_Term.rng q)
in (match (uu____759) with
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

let uu____802 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____802) with
| (labels, body) -> begin
(let _0_601 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_0_601)))
end))
end))
in (aux "assertion failed" None None [] q)))
end)))))))


let detail_errors : FStar_TypeChecker_Env.env  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  ((FStar_SMTEncoding_Z3.unsat_core, (FStar_SMTEncoding_Term.error_labels * FStar_SMTEncoding_Z3.error_kind)) FStar_Util.either * Prims.int))  ->  FStar_SMTEncoding_Term.error_labels = (fun env all_labels askZ3 -> (

let print_banner = (fun uu____847 -> (let _0_604 = (FStar_Range.string_of_range (FStar_TypeChecker_Env.get_range env))
in (let _0_603 = (FStar_Util.string_of_int (Prims.parse_int "5"))
in (let _0_602 = (FStar_Util.string_of_int (FStar_List.length all_labels))
in (FStar_Util.print3_error "Detailed error report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n" _0_604 _0_603 _0_602)))))
in (

let print_result = (fun uu____859 -> (match (uu____859) with
| ((uu____865, msg, r), success) -> begin
(match (success) with
| true -> begin
(let _0_605 = (FStar_Range.string_of_range r)
in (FStar_Util.print1_error "OK: proof obligation at %s was proven\n" _0_605))
end
| uu____872 -> begin
(FStar_Errors.report r msg)
end)
end))
in (

let elim = (fun labs -> (FStar_All.pipe_right labs (FStar_List.map (fun uu____902 -> (match (uu____902) with
| (l, uu____909, uu____910) -> begin
FStar_SMTEncoding_Term.Assume ((let _0_607 = (FStar_SMTEncoding_Util.mkEq (let _0_606 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((_0_606), (FStar_SMTEncoding_Util.mkTrue))))
in ((_0_607), (Some ("Disabling label")), (Some ((Prims.strcat "disable_label_" (Prims.fst l)))))))
end)))))
in (

let rec linear_check = (fun eliminated errors active -> (match (active) with
| [] -> begin
(

let results = (let _0_609 = (FStar_List.map (fun x -> ((x), (true))) eliminated)
in (let _0_608 = (FStar_List.map (fun x -> ((x), (false))) errors)
in (FStar_List.append _0_609 _0_608)))
in (sort_labels results))
end
| (hd)::tl -> begin
(

let uu____960 = (askZ3 (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl))))
in (match (uu____960) with
| (result, uu____981) -> begin
(

let uu____990 = (FStar_Util.is_left result)
in (match (uu____990) with
| true -> begin
(linear_check ((hd)::eliminated) errors tl)
end
| uu____999 -> begin
(linear_check eliminated ((hd)::errors) tl)
end))
end))
end))
in (print_banner ());
(FStar_Options.set_option "z3rlimit" (FStar_Options.Int ((Prims.parse_int "5"))));
(

let res = (linear_check [] [] all_labels)
in (FStar_All.pipe_right res (FStar_List.iter print_result));
[];
);
)))))





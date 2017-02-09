
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
(let _0_445 = (FStar_Util.string_of_int (FStar_ST.read ctr))
in (FStar_Util.format1 "label_%s" _0_445));
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
| (None, uu____192) -> begin
false
end
| (Some (nm), FStar_SMTEncoding_Term.FreeV (nm', uu____196)) -> begin
(nm = nm')
end
| ((_, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Valid"), (tm)::[]))) | ((_, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("ApplyTT"), (tm)::_))) -> begin
(is_a_post_condition post_name_opt tm)
end
| uu____206 -> begin
false
end))
in (

let conjuncts = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> begin
cs
end
| uu____219 -> begin
(t)::[]
end))
in (

let is_guard_free = (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____225; FStar_SMTEncoding_Term.rng = uu____226})::[])::[], iopt, uu____228, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = uu____231; FStar_SMTEncoding_Term.rng = uu____232}) -> begin
true
end
| uu____251 -> begin
false
end))
in (

let is_a_named_continuation = (fun lhs -> (FStar_All.pipe_right (conjuncts lhs) (FStar_Util.for_some is_guard_free)))
in (

let uu____257 = (match (use_env_msg) with
| None -> begin
((false), (""))
end
| Some (f) -> begin
(let _0_446 = (f ())
in ((true), (_0_446)))
end)
in (match (uu____257) with
| (flag, msg_prefix) -> begin
(

let fresh_label = (fun msg ropt rng t -> (

let msg = (match (flag) with
| true -> begin
(Prims.strcat "Failed to verify implicit argument: " msg)
end
| uu____291 -> begin
msg
end)
in (

let rng = (match (ropt) with
| None -> begin
rng
end
| Some (r) -> begin
(

let uu___99_294 = r
in {FStar_Range.def_range = rng.FStar_Range.def_range; FStar_Range.use_range = uu___99_294.FStar_Range.use_range})
end)
in (fresh_label msg rng t))))
in (

let rec aux = (fun default_msg ropt post_name_opt labels q -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
((labels), (q))
end
| FStar_SMTEncoding_Term.LblPos (uu____326) -> begin
(failwith "Impossible")
end
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", uu____333) -> begin
(

let fallback = (fun msg -> (aux default_msg ropt post_name_opt labels arg))
in try
(match (()) with
| () -> begin
(match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, (post)::sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____357; FStar_SMTEncoding_Term.rng = rng}) -> begin
(

let post_name = (let _0_448 = (let _0_447 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _0_447))
in (Prims.strcat "^^post_condition_" _0_448))
in (

let names = (let _0_451 = (FStar_List.mapi (fun i s -> (let _0_450 = (let _0_449 = (FStar_Util.string_of_int i)
in (Prims.strcat "^^" _0_449))
in ((_0_450), (s)))) sorts)
in (((post_name), (post)))::_0_451)
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names)
in (

let uu____387 = (let _0_453 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (let _0_452 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((_0_453), (_0_452))))
in (match (uu____387) with
| (lhs, rhs) -> begin
(

let uu____395 = (match (lhs.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, clauses_lhs) -> begin
(

let uu____405 = (FStar_Util.prefix clauses_lhs)
in (match (uu____405) with
| (req, ens) -> begin
(match (ens.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats_ens, iopt_ens, sorts_ens, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (ensures_conjuncts)::(post)::[]); FStar_SMTEncoding_Term.freevars = uu____424; FStar_SMTEncoding_Term.rng = rng_ens}) when (is_a_post_condition (Some (post_name)) post) -> begin
(

let uu____439 = (aux "could not prove post-condition" None (Some (post_name)) labels ensures_conjuncts)
in (match (uu____439) with
| (labels, ensures_conjuncts) -> begin
(

let pats_ens = (match (pats_ens) with
| ([]) | (([])::[]) -> begin
((post)::[])::[]
end
| uu____460 -> begin
pats_ens
end)
in (

let ens = (let _0_455 = FStar_SMTEncoding_Term.Quant ((let _0_454 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((ensures_conjuncts)::(post)::[])))) rng_ens)
in ((FStar_SMTEncoding_Term.Forall), (pats_ens), (iopt_ens), (sorts_ens), (_0_454))))
in (FStar_SMTEncoding_Term.mk _0_455 ens.FStar_SMTEncoding_Term.rng))
in (

let lhs = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.And), ((FStar_List.append req ((ens)::[])))))) lhs.FStar_SMTEncoding_Term.rng)
in (let _0_456 = (FStar_SMTEncoding_Term.abstr names lhs)
in ((labels), (_0_456))))))
end))
end
| uu____472 -> begin
(Prims.raise (Not_a_wp_implication ((let _0_459 = (let _0_458 = (let _0_457 = (FStar_SMTEncoding_Term.print_smt_term ens)
in (Prims.strcat "  ... " _0_457))
in (Prims.strcat post_name _0_458))
in (Prims.strcat "Ensures clause doesn\'t match post name:  " _0_459)))))
end)
end))
end
| uu____476 -> begin
(Prims.raise (Not_a_wp_implication ((let _0_460 = (FStar_SMTEncoding_Term.print_smt_term lhs)
in (Prims.strcat "LHS not a conjunct: " _0_460)))))
end)
in (match (uu____395) with
| (labels, lhs) -> begin
(

let uu____487 = (

let uu____491 = (aux default_msg None (Some (post_name)) labels rhs)
in (match (uu____491) with
| (labels, rhs) -> begin
(let _0_461 = (FStar_SMTEncoding_Term.abstr names rhs)
in ((labels), (_0_461)))
end))
in (match (uu____487) with
| (labels, rhs) -> begin
(

let body = (FStar_SMTEncoding_Term.mkImp ((lhs), (rhs)) rng)
in (let _0_462 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), ((post)::sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_0_462))))
end))
end))
end)))))
end
| uu____516 -> begin
(fallback (let _0_463 = (FStar_SMTEncoding_Term.print_smt_term arg)
in (Prims.strcat "arg not a quant: " _0_463)))
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
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, [], None, (post)::[], {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____528; FStar_SMTEncoding_Term.rng = rng}) when (is_a_named_continuation lhs) -> begin
(

let post_name = (let _0_465 = (let _0_464 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _0_464))
in (Prims.strcat "^^post_condition_" _0_465))
in (

let names = ((post_name), (post))
in (

let instantiation = (let _0_466 = (FStar_SMTEncoding_Util.mkFreeV names)
in (_0_466)::[])
in (

let uu____546 = (let _0_468 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (let _0_467 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((_0_468), (_0_467))))
in (match (uu____546) with
| (lhs, rhs) -> begin
(

let uu____554 = (FStar_Util.fold_map (fun labels tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____567; FStar_SMTEncoding_Term.rng = uu____568})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = uu____573; FStar_SMTEncoding_Term.rng = uu____574}) -> begin
(

let uu____593 = (aux default_msg None post_name_opt labels r)
in (match (uu____593) with
| (labels, r) -> begin
(let _0_471 = (let _0_470 = FStar_SMTEncoding_Term.Quant ((let _0_469 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Iff), ((l)::(r)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (Some ((Prims.parse_int "0"))), (sorts), (_0_469))))
in (FStar_SMTEncoding_Term.mk _0_470 q.FStar_SMTEncoding_Term.rng))
in ((labels), (_0_471)))
end))
end
| uu____612 -> begin
((labels), (tm))
end)) labels (conjuncts lhs))
in (match (uu____554) with
| (labels, lhs_conjs) -> begin
(

let uu____623 = (aux default_msg None (Some (post_name)) labels rhs)
in (match (uu____623) with
| (labels, rhs) -> begin
(

let body = (let _0_474 = (let _0_473 = (let _0_472 = (FStar_SMTEncoding_Term.mk_and_l lhs_conjs lhs.FStar_SMTEncoding_Term.rng)
in ((_0_472), (rhs)))
in (FStar_SMTEncoding_Term.mkImp _0_473 rng))
in (FStar_All.pipe_right _0_474 (FStar_SMTEncoding_Term.abstr ((names)::[]))))
in (

let q = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), ([]), (None), ((post)::[]), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (q))))
end))
end))
end)))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let uu____649 = (aux default_msg ropt post_name_opt labels rhs)
in (match (uu____649) with
| (labels, rhs) -> begin
(let _0_475 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs)))
in ((labels), (_0_475)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let uu____664 = (FStar_Util.fold_map (aux default_msg ropt post_name_opt) labels conjuncts)
in (match (uu____664) with
| (labels, conjuncts) -> begin
(let _0_476 = (FStar_SMTEncoding_Term.mk_and_l conjuncts q.FStar_SMTEncoding_Term.rng)
in ((labels), (_0_476)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]) -> begin
(

let uu____684 = (aux default_msg ropt post_name_opt labels q1)
in (match (uu____684) with
| (labels, q1) -> begin
(

let uu____695 = (aux default_msg ropt post_name_opt labels q2)
in (match (uu____695) with
| (labels, q2) -> begin
(let _0_477 = (FStar_SMTEncoding_Term.mkITE ((hd), (q1), (q2)) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_0_477)))
end))
end))
end
| (FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, _, _, _, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, _)) -> begin
(

let uu____719 = (fresh_label default_msg ropt q.FStar_SMTEncoding_Term.rng q)
in (match (uu____719) with
| (lab, q) -> begin
(((lab)::labels), (q))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____728), uu____729) when (is_a_post_condition post_name_opt q) -> begin
((labels), (q))
end
| (FStar_SMTEncoding_Term.FreeV (_)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (_), _)) -> begin
(

let uu____753 = (fresh_label default_msg ropt q.FStar_SMTEncoding_Term.rng q)
in (match (uu____753) with
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

let uu____796 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____796) with
| (labels, body) -> begin
(let _0_478 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_0_478)))
end))
end))
in (aux "assertion failed" None None [] q)))
end)))))))


let detail_errors : FStar_TypeChecker_Env.env  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  ((FStar_SMTEncoding_Z3.unsat_core, (labels * FStar_SMTEncoding_Z3.error_kind)) FStar_Util.either * Prims.int))  ->  labels = (fun env all_labels askZ3 -> (

let print_banner = (fun uu____841 -> (let _0_481 = (FStar_Range.string_of_range (FStar_TypeChecker_Env.get_range env))
in (let _0_480 = (FStar_Util.string_of_int (Prims.parse_int "5"))
in (let _0_479 = (FStar_Util.string_of_int (FStar_List.length all_labels))
in (FStar_Util.print3_error "Detailed error report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n" _0_481 _0_480 _0_479)))))
in (

let print_result = (fun uu____853 -> (match (uu____853) with
| ((uu____859, msg, r), success) -> begin
(match (success) with
| true -> begin
(let _0_482 = (FStar_Range.string_of_range r)
in (FStar_Util.print1_error "OK: proof obligation at %s was proven\n" _0_482))
end
| uu____866 -> begin
(FStar_Errors.report r msg)
end)
end))
in (

let elim = (fun labs -> (FStar_All.pipe_right labs (FStar_List.map (fun uu____896 -> (match (uu____896) with
| (l, uu____903, uu____904) -> begin
FStar_SMTEncoding_Term.Assume ((let _0_484 = (FStar_SMTEncoding_Util.mkEq (let _0_483 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((_0_483), (FStar_SMTEncoding_Util.mkTrue))))
in ((_0_484), (Some ("Disabling label")), (Some ((Prims.strcat "disable_label_" (Prims.fst l)))))))
end)))))
in (

let rec linear_check = (fun eliminated errors active -> (match (active) with
| [] -> begin
(

let results = (let _0_486 = (FStar_List.map (fun x -> ((x), (true))) eliminated)
in (let _0_485 = (FStar_List.map (fun x -> ((x), (false))) errors)
in (FStar_List.append _0_486 _0_485)))
in (sort_labels results))
end
| (hd)::tl -> begin
((let _0_487 = (FStar_Util.string_of_int (FStar_List.length active))
in (FStar_Util.print1 "%s, " _0_487));
(FStar_SMTEncoding_Z3.refresh ());
(

let uu____959 = (askZ3 (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl))))
in (match (uu____959) with
| (result, uu____980) -> begin
(

let uu____989 = (FStar_Util.is_left result)
in (match (uu____989) with
| true -> begin
(linear_check ((hd)::eliminated) errors tl)
end
| uu____998 -> begin
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





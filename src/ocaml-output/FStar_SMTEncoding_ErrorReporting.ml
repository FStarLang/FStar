
open Prims
open FStar_Pervasives
exception Not_a_wp_implication of (Prims.string)


let uu___is_Not_a_wp_implication : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not_a_wp_implication (uu____8) -> begin
true
end
| uu____9 -> begin
false
end))


let __proj__Not_a_wp_implication__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Not_a_wp_implication (uu____17) -> begin
uu____17
end))


type label =
FStar_SMTEncoding_Term.error_label


type labels =
FStar_SMTEncoding_Term.error_labels


let sort_labels : (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list  ->  ((FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) * Prims.bool) Prims.list = (fun l -> (FStar_List.sortWith (fun uu____49 uu____50 -> (match (((uu____49), (uu____50))) with
| (((uu____71, uu____72, r1), uu____74), ((uu____75, uu____76, r2), uu____78)) -> begin
(FStar_Range.compare r1 r2)
end)) l))


let remove_dups : labels  ->  (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_Util.remove_dups (fun uu____114 uu____115 -> (match (((uu____114), (uu____115))) with
| ((uu____128, m1, r1), (uu____131, m2, r2)) -> begin
((r1 = r2) && (m1 = m2))
end)) l))


type msg =
(Prims.string * FStar_Range.range)


type ranges =
(Prims.string FStar_Pervasives_Native.option * FStar_Range.range) Prims.list


let fresh_label : Prims.string  ->  FStar_Range.range  ->  FStar_SMTEncoding_Term.term  ->  (label * FStar_SMTEncoding_Term.term) = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun message range t -> (

let l = ((FStar_Util.incr ctr);
(

let uu____168 = (

let uu____169 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int uu____169))
in (FStar_Util.format1 "label_%s" uu____168));
)
in (

let lvar = ((l), (FStar_SMTEncoding_Term.Bool_sort))
in (

let label = ((lvar), (message), (range))
in (

let lterm = (FStar_SMTEncoding_Util.mkFreeV lvar)
in (

let lt1 = (FStar_SMTEncoding_Term.mkOr ((lterm), (t)) range)
in ((label), (lt1)))))))))


let label_goals : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  FStar_SMTEncoding_Term.term  ->  (labels * FStar_SMTEncoding_Term.term) = (fun use_env_msg r q -> (

let rec is_a_post_condition = (fun post_name_opt tm -> (match (((post_name_opt), (tm.FStar_SMTEncoding_Term.tm))) with
| (FStar_Pervasives_Native.None, uu____223) -> begin
false
end
| (FStar_Pervasives_Native.Some (nm), FStar_SMTEncoding_Term.FreeV (nm', uu____227)) -> begin
(nm = nm')
end
| (uu____229, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Valid"), (tm1)::[])) -> begin
(is_a_post_condition post_name_opt tm1)
end
| (uu____234, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("ApplyTT"), (tm1)::uu____236)) -> begin
(is_a_post_condition post_name_opt tm1)
end
| uu____241 -> begin
false
end))
in (

let conjuncts = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> begin
cs
end
| uu____254 -> begin
(t)::[]
end))
in (

let is_guard_free = (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____260; FStar_SMTEncoding_Term.rng = uu____261})::[])::[], iopt, uu____263, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r1)::[]); FStar_SMTEncoding_Term.freevars = uu____266; FStar_SMTEncoding_Term.rng = uu____267}) -> begin
true
end
| uu____286 -> begin
false
end))
in (

let is_a_named_continuation = (fun lhs -> (FStar_All.pipe_right (conjuncts lhs) (FStar_Util.for_some is_guard_free)))
in (

let uu____292 = (match (use_env_msg) with
| FStar_Pervasives_Native.None -> begin
((false), (""))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____304 = (f ())
in ((true), (uu____304)))
end)
in (match (uu____292) with
| (flag, msg_prefix) -> begin
(

let fresh_label1 = (fun msg ropt rng t -> (

let msg1 = (match (flag) with
| true -> begin
(Prims.strcat "Failed to verify implicit argument: " msg)
end
| uu____327 -> begin
msg
end)
in (

let rng1 = (match (ropt) with
| FStar_Pervasives_Native.None -> begin
rng
end
| FStar_Pervasives_Native.Some (r1) -> begin
(

let uu___105_330 = r1
in {FStar_Range.def_range = rng.FStar_Range.def_range; FStar_Range.use_range = uu___105_330.FStar_Range.use_range})
end)
in (fresh_label msg1 rng1 t))))
in (

let rec aux = (fun default_msg ropt post_name_opt labels q1 -> (match (q1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.BoundV (uu____359) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.Integer (uu____361) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.LblPos (uu____363) -> begin
(failwith "Impossible")
end
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", uu____370) -> begin
(

let fallback = (fun msg -> (aux default_msg ropt post_name_opt labels arg))
in try
(match (()) with
| () -> begin
(match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, (post)::sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____417; FStar_SMTEncoding_Term.rng = rng}) -> begin
(

let post_name = (

let uu____433 = (

let uu____434 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____434))
in (Prims.strcat "^^post_condition_" uu____433))
in (

let names1 = (

let uu____439 = (FStar_List.mapi (fun i s -> (

let uu____450 = (

let uu____451 = (FStar_Util.string_of_int i)
in (Prims.strcat "^^" uu____451))
in ((uu____450), (s)))) sorts)
in (((post_name), (post)))::uu____439)
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1)
in (

let uu____458 = (

let uu____461 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____462 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____461), (uu____462))))
in (match (uu____458) with
| (lhs1, rhs1) -> begin
(

let uu____468 = (match (lhs1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, clauses_lhs) -> begin
(

let uu____478 = (FStar_Util.prefix clauses_lhs)
in (match (uu____478) with
| (req, ens) -> begin
(match (ens.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats_ens, iopt_ens, sorts_ens, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (ensures_conjuncts)::(post1)::[]); FStar_SMTEncoding_Term.freevars = uu____497; FStar_SMTEncoding_Term.rng = rng_ens}) when (is_a_post_condition (FStar_Pervasives_Native.Some (post_name)) post1) -> begin
(

let uu____512 = (aux "could not prove post-condition" FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels ensures_conjuncts)
in (match (uu____512) with
| (labels1, ensures_conjuncts1) -> begin
(

let pats_ens1 = (match (pats_ens) with
| [] -> begin
((post1)::[])::[]
end
| ([])::[] -> begin
((post1)::[])::[]
end
| uu____535 -> begin
pats_ens
end)
in (

let ens1 = (

let uu____539 = (

let uu____540 = (

let uu____550 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((ensures_conjuncts1)::(post1)::[])))) rng_ens)
in ((FStar_SMTEncoding_Term.Forall), (pats_ens1), (iopt_ens), (sorts_ens), (uu____550)))
in FStar_SMTEncoding_Term.Quant (uu____540))
in (FStar_SMTEncoding_Term.mk uu____539 ens.FStar_SMTEncoding_Term.rng))
in (

let lhs2 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.And), ((FStar_List.append req ((ens1)::[])))))) lhs1.FStar_SMTEncoding_Term.rng)
in (

let uu____558 = (FStar_SMTEncoding_Term.abstr names1 lhs2)
in ((labels1), (uu____558))))))
end))
end
| uu____560 -> begin
(

let uu____561 = (

let uu____562 = (

let uu____563 = (

let uu____564 = (

let uu____565 = (FStar_SMTEncoding_Term.print_smt_term ens)
in (Prims.strcat "  ... " uu____565))
in (Prims.strcat post_name uu____564))
in (Prims.strcat "Ensures clause doesn\'t match post name:  " uu____563))
in Not_a_wp_implication (uu____562))
in (FStar_Pervasives.raise uu____561))
end)
end))
end
| uu____569 -> begin
(

let uu____570 = (

let uu____571 = (

let uu____572 = (FStar_SMTEncoding_Term.print_smt_term lhs1)
in (Prims.strcat "LHS not a conjunct: " uu____572))
in Not_a_wp_implication (uu____571))
in (FStar_Pervasives.raise uu____570))
end)
in (match (uu____468) with
| (labels1, lhs2) -> begin
(

let uu____583 = (

let uu____587 = (aux default_msg FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels1 rhs1)
in (match (uu____587) with
| (labels2, rhs2) -> begin
(

let uu____598 = (FStar_SMTEncoding_Term.abstr names1 rhs2)
in ((labels2), (uu____598)))
end))
in (match (uu____583) with
| (labels2, rhs2) -> begin
(

let body = (FStar_SMTEncoding_Term.mkImp ((lhs2), (rhs2)) rng)
in (

let uu____608 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), ((post)::sorts), (body)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (uu____608))))
end))
end))
end)))))
end
| uu____614 -> begin
(

let uu____615 = (

let uu____616 = (FStar_SMTEncoding_Term.print_smt_term arg)
in (Prims.strcat "arg not a quant: " uu____616))
in (fallback uu____615))
end)
end)
with
| Not_a_wp_implication (msg) -> begin
(fallback msg)
end)
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r1) -> begin
(aux reason (FStar_Pervasives_Native.Some (r1)) post_name_opt labels arg)
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, [], FStar_Pervasives_Native.None, (post)::[], {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____630; FStar_SMTEncoding_Term.rng = rng}) when (is_a_named_continuation lhs) -> begin
(

let post_name = (

let uu____643 = (

let uu____644 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____644))
in (Prims.strcat "^^post_condition_" uu____643))
in (

let names1 = ((post_name), (post))
in (

let instantiation = (

let uu____650 = (FStar_SMTEncoding_Util.mkFreeV names1)
in (uu____650)::[])
in (

let uu____651 = (

let uu____654 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____655 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____654), (uu____655))))
in (match (uu____651) with
| (lhs1, rhs1) -> begin
(

let uu____661 = (FStar_Util.fold_map (fun labels1 tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____689; FStar_SMTEncoding_Term.rng = uu____690})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r1)::[]); FStar_SMTEncoding_Term.freevars = uu____695; FStar_SMTEncoding_Term.rng = uu____696}) -> begin
(

let uu____715 = (aux default_msg FStar_Pervasives_Native.None post_name_opt labels1 r1)
in (match (uu____715) with
| (labels2, r2) -> begin
(

let uu____726 = (

let uu____727 = (

let uu____728 = (

let uu____738 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Iff), ((l)::(r2)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), (sorts), (uu____738)))
in FStar_SMTEncoding_Term.Quant (uu____728))
in (FStar_SMTEncoding_Term.mk uu____727 q1.FStar_SMTEncoding_Term.rng))
in ((labels2), (uu____726)))
end))
end
| uu____747 -> begin
((labels1), (tm))
end)) labels (conjuncts lhs1))
in (match (uu____661) with
| (labels1, lhs_conjs) -> begin
(

let uu____758 = (aux default_msg FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels1 rhs1)
in (match (uu____758) with
| (labels2, rhs2) -> begin
(

let body = (

let uu____770 = (

let uu____771 = (

let uu____774 = (FStar_SMTEncoding_Term.mk_and_l lhs_conjs lhs1.FStar_SMTEncoding_Term.rng)
in ((uu____774), (rhs2)))
in (FStar_SMTEncoding_Term.mkImp uu____771 rng))
in (FStar_All.pipe_right uu____770 (FStar_SMTEncoding_Term.abstr ((names1)::[]))))
in (

let q2 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), ([]), (FStar_Pervasives_Native.None), ((post)::[]), (body)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (q2))))
end))
end))
end)))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let uu____789 = (aux default_msg ropt post_name_opt labels rhs)
in (match (uu____789) with
| (labels1, rhs1) -> begin
(

let uu____800 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs1)))
in ((labels1), (uu____800)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts1) -> begin
(

let uu____805 = (FStar_Util.fold_map (aux default_msg ropt post_name_opt) labels conjuncts1)
in (match (uu____805) with
| (labels1, conjuncts2) -> begin
(

let uu____820 = (FStar_SMTEncoding_Term.mk_and_l conjuncts2 q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____820)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd1)::(q11)::(q2)::[]) -> begin
(

let uu____826 = (aux default_msg ropt post_name_opt labels q11)
in (match (uu____826) with
| (labels1, q12) -> begin
(

let uu____837 = (aux default_msg ropt post_name_opt labels1 q2)
in (match (uu____837) with
| (labels2, q21) -> begin
(

let uu____848 = (FStar_SMTEncoding_Term.mkITE ((hd1), (q12), (q21)) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (uu____848)))
end))
end))
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, uu____850, uu____851, uu____852, uu____853) -> begin
(

let uu____862 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____862) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, uu____871) -> begin
(

let uu____874 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____874) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, uu____883) -> begin
(

let uu____886 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____886) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____895), uu____896) when (is_a_post_condition post_name_opt q1) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.FreeV (uu____900) -> begin
(

let uu____903 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____903) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____912) -> begin
(

let uu____915 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____915) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____924) -> begin
(

let uu____927 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____927) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, uu____936) -> begin
(

let uu____939 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____939) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, uu____948) -> begin
(

let uu____951 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____951) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, uu____960) -> begin
(

let uu____963 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____963) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, uu____972) -> begin
(

let uu____975 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____975) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, uu____984) -> begin
(

let uu____987 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____987) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, uu____996) -> begin
(

let uu____999 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____999) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____1008), uu____1009) -> begin
(

let uu____1012 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1012) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Add, uu____1021) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Sub, uu____1027) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Div, uu____1033) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mul, uu____1039) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Minus, uu____1045) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mod, uu____1051) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvAnd, uu____1057) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvXor, uu____1063) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvOr, uu____1069) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvShl, uu____1075) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvShr, uu____1081) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUdiv, uu____1087) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvMod, uu____1093) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.NatToBv (uu____1099), uu____1100) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, uu____1106) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, uu____1112) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body) -> begin
(

let uu____1130 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____1130) with
| (labels1, body1) -> begin
(

let uu____1141 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body1)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____1141)))
end))
end
| FStar_SMTEncoding_Term.Let (es, body) -> begin
(

let uu____1151 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____1151) with
| (labels1, body1) -> begin
(

let uu____1162 = (FStar_SMTEncoding_Term.mkLet ((es), (body1)) q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____1162)))
end))
end))
in (aux "assertion failed" FStar_Pervasives_Native.None FStar_Pervasives_Native.None [] q)))
end)))))))


let detail_errors : FStar_TypeChecker_Env.env  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  ((FStar_SMTEncoding_Z3.unsat_core, (labels * FStar_SMTEncoding_Z3.error_kind)) FStar_Util.either * Prims.int * FStar_SMTEncoding_Z3.z3statistics))  ->  labels = (fun env all_labels askZ3 -> (

let print_banner = (fun uu____1199 -> (

let uu____1200 = (

let uu____1201 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____1201))
in (

let uu____1202 = (FStar_Util.string_of_int (Prims.parse_int "5"))
in (

let uu____1203 = (FStar_Util.string_of_int (FStar_List.length all_labels))
in (FStar_Util.print3_error "Detailed error report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n" uu____1200 uu____1202 uu____1203)))))
in (

let print_result = (fun uu____1218 -> (match (uu____1218) with
| ((uu____1224, msg, r), success) -> begin
(match (success) with
| true -> begin
(

let uu____1231 = (FStar_Range.string_of_range r)
in (FStar_Util.print1_error "OK: proof obligation at %s was proven\n" uu____1231))
end
| uu____1232 -> begin
(FStar_Errors.err r msg)
end)
end))
in (

let elim = (fun labs -> (FStar_All.pipe_right labs (FStar_List.map (fun uu____1267 -> (match (uu____1267) with
| (l, uu____1274, uu____1275) -> begin
(

let a = (

let uu____1281 = (

let uu____1282 = (

let uu____1285 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((uu____1285), (FStar_SMTEncoding_Util.mkTrue)))
in (FStar_SMTEncoding_Util.mkEq uu____1282))
in {FStar_SMTEncoding_Term.assumption_term = uu____1281; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("Disabling label"); FStar_SMTEncoding_Term.assumption_name = (Prims.strcat "disable_label_" (FStar_Pervasives_Native.fst l)); FStar_SMTEncoding_Term.assumption_fact_ids = []})
in FStar_SMTEncoding_Term.Assume (a))
end)))))
in (

let rec linear_check = (fun eliminated errors active -> (match (active) with
| [] -> begin
(

let results = (

let uu____1318 = (FStar_List.map (fun x -> ((x), (true))) eliminated)
in (

let uu____1326 = (FStar_List.map (fun x -> ((x), (false))) errors)
in (FStar_List.append uu____1318 uu____1326)))
in (sort_labels results))
end
| (hd1)::tl1 -> begin
((

let uu____1340 = (FStar_Util.string_of_int (FStar_List.length active))
in (FStar_Util.print1 "%s, " uu____1340));
(FStar_SMTEncoding_Z3.refresh ());
(

let uu____1348 = (

let uu____1356 = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl1)))
in (askZ3 uu____1356))
in (match (uu____1348) with
| (result, uu____1371, uu____1372) -> begin
(

let uu____1381 = (FStar_Util.is_left result)
in (match (uu____1381) with
| true -> begin
(linear_check ((hd1)::eliminated) errors tl1)
end
| uu____1390 -> begin
(linear_check eliminated ((hd1)::errors) tl1)
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





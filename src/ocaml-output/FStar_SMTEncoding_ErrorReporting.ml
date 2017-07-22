
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


let sort_labels : (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list  ->  ((FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) * Prims.bool) Prims.list = (fun l -> (FStar_List.sortWith (fun uu____66 uu____67 -> (match (((uu____66), (uu____67))) with
| (((uu____108, uu____109, r1), uu____111), ((uu____112, uu____113, r2), uu____115)) -> begin
(FStar_Range.compare r1 r2)
end)) l))


let remove_dups : labels  ->  (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_Util.remove_dups (fun uu____174 uu____175 -> (match (((uu____174), (uu____175))) with
| ((uu____200, m1, r1), (uu____203, m2, r2)) -> begin
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

let uu____254 = (

let uu____255 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int uu____255))
in (FStar_Util.format1 "label_%s" uu____254));
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
| (FStar_Pervasives_Native.None, uu____332) -> begin
false
end
| (FStar_Pervasives_Native.Some (nm), FStar_SMTEncoding_Term.FreeV (nm', uu____337)) -> begin
(nm = nm')
end
| (uu____340, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Valid"), (tm1)::[])) -> begin
(is_a_post_condition post_name_opt tm1)
end
| (uu____348, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("ApplyTT"), (tm1)::uu____350)) -> begin
(is_a_post_condition post_name_opt tm1)
end
| uu____359 -> begin
false
end))
in (

let conjuncts = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> begin
cs
end
| uu____379 -> begin
(t)::[]
end))
in (

let is_guard_free = (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____385; FStar_SMTEncoding_Term.rng = uu____386})::[])::[], iopt, uu____388, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r1)::[]); FStar_SMTEncoding_Term.freevars = uu____391; FStar_SMTEncoding_Term.rng = uu____392}) -> begin
true
end
| uu____429 -> begin
false
end))
in (

let is_a_named_continuation = (fun lhs -> (FStar_All.pipe_right (conjuncts lhs) (FStar_Util.for_some is_guard_free)))
in (

let uu____436 = (match (use_env_msg) with
| FStar_Pervasives_Native.None -> begin
((false), (""))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____452 = (f ())
in ((true), (uu____452)))
end)
in (match (uu____436) with
| (flag, msg_prefix) -> begin
(

let fresh_label1 = (fun msg ropt rng t -> (

let msg1 = (match (flag) with
| true -> begin
(Prims.strcat "Failed to verify implicit argument: " msg)
end
| uu____481 -> begin
msg
end)
in (

let rng1 = (match (ropt) with
| FStar_Pervasives_Native.None -> begin
rng
end
| FStar_Pervasives_Native.Some (r1) -> begin
(

let uu___105_484 = r1
in {FStar_Range.def_range = rng.FStar_Range.def_range; FStar_Range.use_range = uu___105_484.FStar_Range.use_range})
end)
in (fresh_label msg1 rng1 t))))
in (

let rec aux = (fun default_msg ropt post_name_opt labels q1 -> (match (q1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.BoundV (uu____525) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.Integer (uu____528) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.LblPos (uu____531) -> begin
(failwith "Impossible")
end
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", uu____543) -> begin
(

let fallback = (fun msg -> (aux default_msg ropt post_name_opt labels arg))
in try
(match (()) with
| () -> begin
(match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, (post)::sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____602; FStar_SMTEncoding_Term.rng = rng}) -> begin
(

let post_name = (

let uu____631 = (

let uu____632 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____632))
in (Prims.strcat "^^post_condition_" uu____631))
in (

let names1 = (

let uu____640 = (FStar_List.mapi (fun i s -> (

let uu____656 = (

let uu____657 = (FStar_Util.string_of_int i)
in (Prims.strcat "^^" uu____657))
in ((uu____656), (s)))) sorts)
in (((post_name), (post)))::uu____640)
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1)
in (

let uu____669 = (

let uu____674 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____675 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____674), (uu____675))))
in (match (uu____669) with
| (lhs1, rhs1) -> begin
(

let uu____684 = (match (lhs1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, clauses_lhs) -> begin
(

let uu____702 = (FStar_Util.prefix clauses_lhs)
in (match (uu____702) with
| (req, ens) -> begin
(match (ens.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats_ens, iopt_ens, sorts_ens, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (ensures_conjuncts)::(post1)::[]); FStar_SMTEncoding_Term.freevars = uu____732; FStar_SMTEncoding_Term.rng = rng_ens}) when (is_a_post_condition (FStar_Pervasives_Native.Some (post_name)) post1) -> begin
(

let uu____760 = (aux "could not prove post-condition" FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels ensures_conjuncts)
in (match (uu____760) with
| (labels1, ensures_conjuncts1) -> begin
(

let pats_ens1 = (match (pats_ens) with
| [] -> begin
((post1)::[])::[]
end
| ([])::[] -> begin
((post1)::[])::[]
end
| uu____802 -> begin
pats_ens
end)
in (

let ens1 = (

let uu____808 = (

let uu____809 = (

let uu____828 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((ensures_conjuncts1)::(post1)::[])))) rng_ens)
in ((FStar_SMTEncoding_Term.Forall), (pats_ens1), (iopt_ens), (sorts_ens), (uu____828)))
in FStar_SMTEncoding_Term.Quant (uu____809))
in (FStar_SMTEncoding_Term.mk uu____808 ens.FStar_SMTEncoding_Term.rng))
in (

let lhs2 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.And), ((FStar_List.append req ((ens1)::[])))))) lhs1.FStar_SMTEncoding_Term.rng)
in (

let uu____842 = (FStar_SMTEncoding_Term.abstr names1 lhs2)
in ((labels1), (uu____842))))))
end))
end
| uu____845 -> begin
(

let uu____846 = (

let uu____847 = (

let uu____848 = (

let uu____849 = (

let uu____850 = (FStar_SMTEncoding_Term.print_smt_term ens)
in (Prims.strcat "  ... " uu____850))
in (Prims.strcat post_name uu____849))
in (Prims.strcat "Ensures clause doesn\'t match post name:  " uu____848))
in Not_a_wp_implication (uu____847))
in (FStar_Pervasives.raise uu____846))
end)
end))
end
| uu____857 -> begin
(

let uu____858 = (

let uu____859 = (

let uu____860 = (FStar_SMTEncoding_Term.print_smt_term lhs1)
in (Prims.strcat "LHS not a conjunct: " uu____860))
in Not_a_wp_implication (uu____859))
in (FStar_Pervasives.raise uu____858))
end)
in (match (uu____684) with
| (labels1, lhs2) -> begin
(

let uu____879 = (

let uu____886 = (aux default_msg FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels1 rhs1)
in (match (uu____886) with
| (labels2, rhs2) -> begin
(

let uu____905 = (FStar_SMTEncoding_Term.abstr names1 rhs2)
in ((labels2), (uu____905)))
end))
in (match (uu____879) with
| (labels2, rhs2) -> begin
(

let body = (FStar_SMTEncoding_Term.mkImp ((lhs2), (rhs2)) rng)
in (

let uu____921 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), ((post)::sorts), (body)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (uu____921))))
end))
end))
end)))))
end
| uu____932 -> begin
(

let uu____933 = (

let uu____934 = (FStar_SMTEncoding_Term.print_smt_term arg)
in (Prims.strcat "arg not a quant: " uu____934))
in (fallback uu____933))
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
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, [], FStar_Pervasives_Native.None, (post)::[], {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____951; FStar_SMTEncoding_Term.rng = rng}) when (is_a_named_continuation lhs) -> begin
(

let post_name = (

let uu____974 = (

let uu____975 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____975))
in (Prims.strcat "^^post_condition_" uu____974))
in (

let names1 = ((post_name), (post))
in (

let instantiation = (

let uu____984 = (FStar_SMTEncoding_Util.mkFreeV names1)
in (uu____984)::[])
in (

let uu____985 = (

let uu____990 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____991 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____990), (uu____991))))
in (match (uu____985) with
| (lhs1, rhs1) -> begin
(

let uu____1000 = (FStar_Util.fold_map (fun labels1 tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____1037; FStar_SMTEncoding_Term.rng = uu____1038})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r1)::[]); FStar_SMTEncoding_Term.freevars = uu____1043; FStar_SMTEncoding_Term.rng = uu____1044}) -> begin
(

let uu____1081 = (aux default_msg FStar_Pervasives_Native.None post_name_opt labels1 r1)
in (match (uu____1081) with
| (labels2, r2) -> begin
(

let uu____1100 = (

let uu____1101 = (

let uu____1102 = (

let uu____1121 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Iff), ((l)::(r2)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), (sorts), (uu____1121)))
in FStar_SMTEncoding_Term.Quant (uu____1102))
in (FStar_SMTEncoding_Term.mk uu____1101 q1.FStar_SMTEncoding_Term.rng))
in ((labels2), (uu____1100)))
end))
end
| uu____1138 -> begin
((labels1), (tm))
end)) labels (conjuncts lhs1))
in (match (uu____1000) with
| (labels1, lhs_conjs) -> begin
(

let uu____1157 = (aux default_msg FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels1 rhs1)
in (match (uu____1157) with
| (labels2, rhs2) -> begin
(

let body = (

let uu____1177 = (

let uu____1178 = (

let uu____1183 = (FStar_SMTEncoding_Term.mk_and_l lhs_conjs lhs1.FStar_SMTEncoding_Term.rng)
in ((uu____1183), (rhs2)))
in (FStar_SMTEncoding_Term.mkImp uu____1178 rng))
in (FStar_All.pipe_right uu____1177 (FStar_SMTEncoding_Term.abstr ((names1)::[]))))
in (

let q2 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), ([]), (FStar_Pervasives_Native.None), ((post)::[]), (body)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (q2))))
end))
end))
end)))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let uu____1209 = (aux default_msg ropt post_name_opt labels rhs)
in (match (uu____1209) with
| (labels1, rhs1) -> begin
(

let uu____1228 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs1)))
in ((labels1), (uu____1228)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts1) -> begin
(

let uu____1236 = (FStar_Util.fold_map (aux default_msg ropt post_name_opt) labels conjuncts1)
in (match (uu____1236) with
| (labels1, conjuncts2) -> begin
(

let uu____1263 = (FStar_SMTEncoding_Term.mk_and_l conjuncts2 q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____1263)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd1)::(q11)::(q2)::[]) -> begin
(

let uu____1271 = (aux default_msg ropt post_name_opt labels q11)
in (match (uu____1271) with
| (labels1, q12) -> begin
(

let uu____1290 = (aux default_msg ropt post_name_opt labels1 q2)
in (match (uu____1290) with
| (labels2, q21) -> begin
(

let uu____1309 = (FStar_SMTEncoding_Term.mkITE ((hd1), (q12), (q21)) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (uu____1309)))
end))
end))
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, uu____1312, uu____1313, uu____1314, uu____1315) -> begin
(

let uu____1332 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1332) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, uu____1347) -> begin
(

let uu____1352 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1352) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, uu____1367) -> begin
(

let uu____1372 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1372) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____1387), uu____1388) when (is_a_post_condition post_name_opt q1) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.FreeV (uu____1395) -> begin
(

let uu____1400 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1400) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____1415) -> begin
(

let uu____1420 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1420) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____1435) -> begin
(

let uu____1440 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1440) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, uu____1455) -> begin
(

let uu____1460 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1460) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, uu____1475) -> begin
(

let uu____1480 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1480) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, uu____1495) -> begin
(

let uu____1500 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1500) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, uu____1515) -> begin
(

let uu____1520 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1520) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, uu____1535) -> begin
(

let uu____1540 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1540) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, uu____1555) -> begin
(

let uu____1560 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1560) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUlt, uu____1575) -> begin
(

let uu____1580 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1580) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____1595), uu____1596) -> begin
(

let uu____1601 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1601) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Add, uu____1616) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Sub, uu____1627) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Div, uu____1638) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mul, uu____1649) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Minus, uu____1660) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mod, uu____1671) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvAnd, uu____1682) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvXor, uu____1693) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvOr, uu____1704) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvShl, uu____1715) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvShr, uu____1726) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUdiv, uu____1737) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvMod, uu____1748) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvMul, uu____1759) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUext (uu____1770), uu____1771) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvToNat, uu____1782) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.NatToBv (uu____1793), uu____1794) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, uu____1805) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, uu____1816) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body) -> begin
(

let uu____1847 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____1847) with
| (labels1, body1) -> begin
(

let uu____1866 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body1)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____1866)))
end))
end
| FStar_SMTEncoding_Term.Let (es, body) -> begin
(

let uu____1883 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____1883) with
| (labels1, body1) -> begin
(

let uu____1902 = (FStar_SMTEncoding_Term.mkLet ((es), (body1)) q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____1902)))
end))
end))
in (aux "assertion failed" FStar_Pervasives_Native.None FStar_Pervasives_Native.None [] q)))
end)))))))


let detail_errors : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  ((FStar_SMTEncoding_Z3.unsat_core, (labels * FStar_SMTEncoding_Z3.error_kind)) FStar_Util.either * Prims.int * FStar_SMTEncoding_Z3.z3statistics))  ->  Prims.unit = (fun hint_replay env all_labels askZ3 -> (

let print_banner = (fun uu____1959 -> (

let msg = (

let uu____1961 = (

let uu____1962 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____1962))
in (

let uu____1963 = (FStar_Util.string_of_int (Prims.parse_int "5"))
in (

let uu____1964 = (FStar_Util.string_of_int (FStar_List.length all_labels))
in (FStar_Util.format4 "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n" (match (hint_replay) with
| true -> begin
"hint replay"
end
| uu____1965 -> begin
"error"
end) uu____1961 uu____1963 uu____1964))))
in (FStar_Util.print_error msg)))
in (

let print_result = (fun uu____1979 -> (match (uu____1979) with
| ((uu____1990, msg, r), success) -> begin
(match (success) with
| true -> begin
(

let uu____2000 = (FStar_Range.string_of_range r)
in (FStar_Util.print1_error "OK: proof obligation at %s was proven\n" uu____2000))
end
| uu____2001 -> begin
(match (hint_replay) with
| true -> begin
(FStar_Errors.warn r (Prims.strcat "Hint failed to replay this sub-proof: " msg))
end
| uu____2002 -> begin
(FStar_Errors.err r msg)
end)
end)
end))
in (

let elim = (fun labs -> (FStar_All.pipe_right labs (FStar_List.map (fun uu____2062 -> (match (uu____2062) with
| (l, uu____2074, uu____2075) -> begin
(

let a = (

let uu____2085 = (

let uu____2086 = (

let uu____2091 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((uu____2091), (FStar_SMTEncoding_Util.mkTrue)))
in (FStar_SMTEncoding_Util.mkEq uu____2086))
in {FStar_SMTEncoding_Term.assumption_term = uu____2085; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("Disabling label"); FStar_SMTEncoding_Term.assumption_name = (Prims.strcat "@disable_label_" (FStar_Pervasives_Native.fst l)); FStar_SMTEncoding_Term.assumption_fact_ids = []})
in FStar_SMTEncoding_Term.Assume (a))
end)))))
in (

let rec linear_check = (fun eliminated errors active -> ((FStar_SMTEncoding_Z3.refresh ());
(match (active) with
| [] -> begin
(

let results = (

let uu____2146 = (FStar_List.map (fun x -> ((x), (true))) eliminated)
in (

let uu____2159 = (FStar_List.map (fun x -> ((x), (false))) errors)
in (FStar_List.append uu____2146 uu____2159)))
in (sort_labels results))
end
| (hd1)::tl1 -> begin
((

let uu____2181 = (FStar_Util.string_of_int (FStar_List.length active))
in (FStar_Util.print1 "%s, " uu____2181));
(

let decls = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl1)))
in (

let uu____2199 = (askZ3 decls)
in (match (uu____2199) with
| (result, uu____2227, uu____2228) -> begin
(

let uu____2245 = (FStar_Util.is_left result)
in (match (uu____2245) with
| true -> begin
(linear_check ((hd1)::eliminated) errors tl1)
end
| uu____2262 -> begin
(linear_check eliminated ((hd1)::errors) tl1)
end))
end)));
)
end);
))
in ((print_banner ());
(FStar_Options.set_option "z3rlimit" (FStar_Options.Int ((Prims.parse_int "5"))));
(

let res = (linear_check [] [] all_labels)
in ((FStar_Util.print_string "\n");
(FStar_All.pipe_right res (FStar_List.iter print_result));
));
))))))





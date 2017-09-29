
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
((Prims.op_Equality r1 r2) && (Prims.op_Equality m1 m2))
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

let uu____272 = (

let uu____273 = (FStar_ST.op_Bang ctr)
in (FStar_Util.string_of_int uu____273))
in (FStar_Util.format1 "label_%s" uu____272));
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
| (FStar_Pervasives_Native.None, uu____408) -> begin
false
end
| (FStar_Pervasives_Native.Some (nm), FStar_SMTEncoding_Term.FreeV (nm', uu____413)) -> begin
(Prims.op_Equality nm nm')
end
| (uu____416, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Valid"), (tm1)::[])) -> begin
(is_a_post_condition post_name_opt tm1)
end
| (uu____424, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("ApplyTT"), (tm1)::uu____426)) -> begin
(is_a_post_condition post_name_opt tm1)
end
| uu____435 -> begin
false
end))
in (

let conjuncts = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> begin
cs
end
| uu____455 -> begin
(t)::[]
end))
in (

let is_guard_free = (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____461; FStar_SMTEncoding_Term.rng = uu____462})::[])::[], iopt, uu____464, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r1)::[]); FStar_SMTEncoding_Term.freevars = uu____467; FStar_SMTEncoding_Term.rng = uu____468}) -> begin
true
end
| uu____505 -> begin
false
end))
in (

let is_a_named_continuation = (fun lhs -> (FStar_All.pipe_right (conjuncts lhs) (FStar_Util.for_some is_guard_free)))
in (

let uu____512 = (match (use_env_msg) with
| FStar_Pervasives_Native.None -> begin
((false), (""))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____528 = (f ())
in ((true), (uu____528)))
end)
in (match (uu____512) with
| (flag, msg_prefix) -> begin
(

let fresh_label1 = (fun msg ropt rng t -> (

let msg1 = (match (flag) with
| true -> begin
(Prims.strcat "Failed to verify implicit argument: " msg)
end
| uu____557 -> begin
msg
end)
in (

let rng1 = (match (ropt) with
| FStar_Pervasives_Native.None -> begin
rng
end
| FStar_Pervasives_Native.Some (r1) -> begin
(

let uu___109_560 = r1
in {FStar_Range.def_range = rng.FStar_Range.def_range; FStar_Range.use_range = uu___109_560.FStar_Range.use_range})
end)
in (fresh_label msg1 rng1 t))))
in (

let rec aux = (fun default_msg ropt post_name_opt labels q1 -> (match (q1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.BoundV (uu____601) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.Integer (uu____604) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.LblPos (uu____607) -> begin
(failwith "Impossible")
end
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", uu____619) -> begin
(

let fallback = (fun msg -> (aux default_msg ropt post_name_opt labels arg))
in (FStar_All.try_with (fun uu___111_659 -> (match (()) with
| () -> begin
(match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, (post)::sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____678; FStar_SMTEncoding_Term.rng = rng}) -> begin
(

let post_name = (

let uu____707 = (

let uu____708 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____708))
in (Prims.strcat "^^post_condition_" uu____707))
in (

let names1 = (

let uu____716 = (FStar_List.mapi (fun i s -> (

let uu____732 = (

let uu____733 = (FStar_Util.string_of_int i)
in (Prims.strcat "^^" uu____733))
in ((uu____732), (s)))) sorts)
in (((post_name), (post)))::uu____716)
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1)
in (

let uu____745 = (

let uu____750 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____751 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____750), (uu____751))))
in (match (uu____745) with
| (lhs1, rhs1) -> begin
(

let uu____760 = (match (lhs1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, clauses_lhs) -> begin
(

let uu____778 = (FStar_Util.prefix clauses_lhs)
in (match (uu____778) with
| (req, ens) -> begin
(match (ens.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats_ens, iopt_ens, sorts_ens, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (ensures_conjuncts)::(post1)::[]); FStar_SMTEncoding_Term.freevars = uu____808; FStar_SMTEncoding_Term.rng = rng_ens}) when (is_a_post_condition (FStar_Pervasives_Native.Some (post_name)) post1) -> begin
(

let uu____836 = (aux "could not prove post-condition" FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels ensures_conjuncts)
in (match (uu____836) with
| (labels1, ensures_conjuncts1) -> begin
(

let pats_ens1 = (match (pats_ens) with
| [] -> begin
((post1)::[])::[]
end
| ([])::[] -> begin
((post1)::[])::[]
end
| uu____878 -> begin
pats_ens
end)
in (

let ens1 = (

let uu____884 = (

let uu____885 = (

let uu____904 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((ensures_conjuncts1)::(post1)::[])))) rng_ens)
in ((FStar_SMTEncoding_Term.Forall), (pats_ens1), (iopt_ens), (sorts_ens), (uu____904)))
in FStar_SMTEncoding_Term.Quant (uu____885))
in (FStar_SMTEncoding_Term.mk uu____884 ens.FStar_SMTEncoding_Term.rng))
in (

let lhs2 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.And), ((FStar_List.append req ((ens1)::[])))))) lhs1.FStar_SMTEncoding_Term.rng)
in (

let uu____918 = (FStar_SMTEncoding_Term.abstr names1 lhs2)
in ((labels1), (uu____918))))))
end))
end
| uu____921 -> begin
(

let uu____922 = (

let uu____923 = (

let uu____924 = (

let uu____925 = (

let uu____926 = (FStar_SMTEncoding_Term.print_smt_term ens)
in (Prims.strcat "  ... " uu____926))
in (Prims.strcat post_name uu____925))
in (Prims.strcat "Ensures clause doesn\'t match post name:  " uu____924))
in Not_a_wp_implication (uu____923))
in (FStar_Exn.raise uu____922))
end)
end))
end
| uu____933 -> begin
(

let uu____934 = (

let uu____935 = (

let uu____936 = (FStar_SMTEncoding_Term.print_smt_term lhs1)
in (Prims.strcat "LHS not a conjunct: " uu____936))
in Not_a_wp_implication (uu____935))
in (FStar_Exn.raise uu____934))
end)
in (match (uu____760) with
| (labels1, lhs2) -> begin
(

let uu____955 = (

let uu____962 = (aux default_msg FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels1 rhs1)
in (match (uu____962) with
| (labels2, rhs2) -> begin
(

let uu____981 = (FStar_SMTEncoding_Term.abstr names1 rhs2)
in ((labels2), (uu____981)))
end))
in (match (uu____955) with
| (labels2, rhs2) -> begin
(

let body = (FStar_SMTEncoding_Term.mkImp ((lhs2), (rhs2)) rng)
in (

let uu____997 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), ((post)::sorts), (body)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (uu____997))))
end))
end))
end)))))
end
| uu____1008 -> begin
(

let uu____1009 = (

let uu____1010 = (FStar_SMTEncoding_Term.print_smt_term arg)
in (Prims.strcat "arg not a quant: " uu____1010))
in (fallback uu____1009))
end)
end)) (fun uu___110_1013 -> (match (uu___110_1013) with
| Not_a_wp_implication (msg) -> begin
(fallback msg)
end))))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r1) -> begin
(aux reason (FStar_Pervasives_Native.Some (r1)) post_name_opt labels arg)
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, [], FStar_Pervasives_Native.None, (post)::[], {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____1027; FStar_SMTEncoding_Term.rng = rng}) when (is_a_named_continuation lhs) -> begin
(

let post_name = (

let uu____1050 = (

let uu____1051 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____1051))
in (Prims.strcat "^^post_condition_" uu____1050))
in (

let names1 = ((post_name), (post))
in (

let instantiation = (

let uu____1060 = (FStar_SMTEncoding_Util.mkFreeV names1)
in (uu____1060)::[])
in (

let uu____1061 = (

let uu____1066 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____1067 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____1066), (uu____1067))))
in (match (uu____1061) with
| (lhs1, rhs1) -> begin
(

let uu____1076 = (FStar_Util.fold_map (fun labels1 tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____1113; FStar_SMTEncoding_Term.rng = uu____1114})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r1)::[]); FStar_SMTEncoding_Term.freevars = uu____1119; FStar_SMTEncoding_Term.rng = uu____1120}) -> begin
(

let uu____1157 = (aux default_msg FStar_Pervasives_Native.None post_name_opt labels1 r1)
in (match (uu____1157) with
| (labels2, r2) -> begin
(

let uu____1176 = (

let uu____1177 = (

let uu____1178 = (

let uu____1197 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Iff), ((l)::(r2)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), (sorts), (uu____1197)))
in FStar_SMTEncoding_Term.Quant (uu____1178))
in (FStar_SMTEncoding_Term.mk uu____1177 q1.FStar_SMTEncoding_Term.rng))
in ((labels2), (uu____1176)))
end))
end
| uu____1214 -> begin
((labels1), (tm))
end)) labels (conjuncts lhs1))
in (match (uu____1076) with
| (labels1, lhs_conjs) -> begin
(

let uu____1233 = (aux default_msg FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels1 rhs1)
in (match (uu____1233) with
| (labels2, rhs2) -> begin
(

let body = (

let uu____1253 = (

let uu____1254 = (

let uu____1259 = (FStar_SMTEncoding_Term.mk_and_l lhs_conjs lhs1.FStar_SMTEncoding_Term.rng)
in ((uu____1259), (rhs2)))
in (FStar_SMTEncoding_Term.mkImp uu____1254 rng))
in (FStar_All.pipe_right uu____1253 (FStar_SMTEncoding_Term.abstr ((names1)::[]))))
in (

let q2 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), ([]), (FStar_Pervasives_Native.None), ((post)::[]), (body)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (q2))))
end))
end))
end)))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let uu____1285 = (aux default_msg ropt post_name_opt labels rhs)
in (match (uu____1285) with
| (labels1, rhs1) -> begin
(

let uu____1304 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs1)))
in ((labels1), (uu____1304)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts1) -> begin
(

let uu____1312 = (FStar_Util.fold_map (aux default_msg ropt post_name_opt) labels conjuncts1)
in (match (uu____1312) with
| (labels1, conjuncts2) -> begin
(

let uu____1339 = (FStar_SMTEncoding_Term.mk_and_l conjuncts2 q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____1339)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd1)::(q11)::(q2)::[]) -> begin
(

let uu____1347 = (aux default_msg ropt post_name_opt labels q11)
in (match (uu____1347) with
| (labels1, q12) -> begin
(

let uu____1366 = (aux default_msg ropt post_name_opt labels1 q2)
in (match (uu____1366) with
| (labels2, q21) -> begin
(

let uu____1385 = (FStar_SMTEncoding_Term.mkITE ((hd1), (q12), (q21)) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (uu____1385)))
end))
end))
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, uu____1388, uu____1389, uu____1390, uu____1391) -> begin
(

let uu____1408 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1408) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, uu____1423) -> begin
(

let uu____1428 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1428) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, uu____1443) -> begin
(

let uu____1448 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1448) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____1463), uu____1464) when (is_a_post_condition post_name_opt q1) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.FreeV (uu____1471) -> begin
(

let uu____1476 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1476) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____1491) -> begin
(

let uu____1496 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1496) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____1511) -> begin
(

let uu____1516 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1516) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, uu____1531) -> begin
(

let uu____1536 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1536) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, uu____1551) -> begin
(

let uu____1556 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1556) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, uu____1571) -> begin
(

let uu____1576 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1576) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, uu____1591) -> begin
(

let uu____1596 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1596) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, uu____1611) -> begin
(

let uu____1616 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1616) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, uu____1631) -> begin
(

let uu____1636 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1636) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUlt, uu____1651) -> begin
(

let uu____1656 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1656) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____1671), uu____1672) -> begin
(

let uu____1677 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1677) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Add, uu____1692) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Sub, uu____1703) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Div, uu____1714) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mul, uu____1725) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Minus, uu____1736) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mod, uu____1747) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvAnd, uu____1758) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvXor, uu____1769) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvOr, uu____1780) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvShl, uu____1791) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvShr, uu____1802) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUdiv, uu____1813) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvMod, uu____1824) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvMul, uu____1835) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUext (uu____1846), uu____1847) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvToNat, uu____1858) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.NatToBv (uu____1869), uu____1870) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, uu____1881) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, uu____1892) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body) -> begin
(

let uu____1923 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____1923) with
| (labels1, body1) -> begin
(

let uu____1942 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body1)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____1942)))
end))
end
| FStar_SMTEncoding_Term.Let (es, body) -> begin
(

let uu____1959 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____1959) with
| (labels1, body1) -> begin
(

let uu____1978 = (FStar_SMTEncoding_Term.mkLet ((es), (body1)) q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____1978)))
end))
end))
in (aux "assertion failed" FStar_Pervasives_Native.None FStar_Pervasives_Native.None [] q)))
end)))))))


let detail_errors : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  FStar_SMTEncoding_Z3.z3result)  ->  Prims.unit = (fun hint_replay env all_labels askZ3 -> (

let print_banner = (fun uu____2007 -> (

let msg = (

let uu____2009 = (

let uu____2010 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____2010))
in (

let uu____2011 = (FStar_Util.string_of_int (Prims.parse_int "5"))
in (

let uu____2012 = (FStar_Util.string_of_int (FStar_List.length all_labels))
in (FStar_Util.format4 "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n" (match (hint_replay) with
| true -> begin
"hint replay"
end
| uu____2013 -> begin
"error"
end) uu____2009 uu____2011 uu____2012))))
in (FStar_Util.print_error msg)))
in (

let print_result = (fun uu____2027 -> (match (uu____2027) with
| ((uu____2038, msg, r), success) -> begin
(match (success) with
| true -> begin
(

let uu____2048 = (FStar_Range.string_of_range r)
in (FStar_Util.print1_error "OK: proof obligation at %s was proven\n" uu____2048))
end
| uu____2049 -> begin
(match (hint_replay) with
| true -> begin
(FStar_Errors.warn r (Prims.strcat "Hint failed to replay this sub-proof: " msg))
end
| uu____2050 -> begin
((

let uu____2052 = (FStar_Range.string_of_range r)
in (FStar_Util.print2_error "XX: proof obligation at %s failed\n\t%s\n" uu____2052 msg));
(FStar_Errors.err r msg);
)
end)
end)
end))
in (

let elim = (fun labs -> (FStar_All.pipe_right labs (FStar_List.map (fun uu____2112 -> (match (uu____2112) with
| (l, uu____2124, uu____2125) -> begin
(

let a = (

let uu____2135 = (

let uu____2136 = (

let uu____2141 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((uu____2141), (FStar_SMTEncoding_Util.mkTrue)))
in (FStar_SMTEncoding_Util.mkEq uu____2136))
in {FStar_SMTEncoding_Term.assumption_term = uu____2135; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("Disabling label"); FStar_SMTEncoding_Term.assumption_name = (Prims.strcat "@disable_label_" (FStar_Pervasives_Native.fst l)); FStar_SMTEncoding_Term.assumption_fact_ids = []})
in FStar_SMTEncoding_Term.Assume (a))
end)))))
in (

let rec linear_check = (fun eliminated errors active -> ((FStar_SMTEncoding_Z3.refresh ());
(match (active) with
| [] -> begin
(

let results = (

let uu____2196 = (FStar_List.map (fun x -> ((x), (true))) eliminated)
in (

let uu____2209 = (FStar_List.map (fun x -> ((x), (false))) errors)
in (FStar_List.append uu____2196 uu____2209)))
in (sort_labels results))
end
| (hd1)::tl1 -> begin
((

let uu____2231 = (FStar_Util.string_of_int (FStar_List.length active))
in (FStar_Util.print1 "%s, " uu____2231));
(

let decls = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl1)))
in (

let uu____2249 = (askZ3 decls)
in (match (uu____2249) with
| (result, uu____2263, uu____2264) -> begin
(match (result) with
| FStar_SMTEncoding_Z3.UNSAT (uu____2277) -> begin
(linear_check ((hd1)::eliminated) errors tl1)
end
| uu____2278 -> begin
(linear_check eliminated ((hd1)::errors) tl1)
end)
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





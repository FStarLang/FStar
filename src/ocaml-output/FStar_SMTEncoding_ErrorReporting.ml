
open Prims
open FStar_Pervasives
exception Not_a_wp_implication of (Prims.string)


let uu___is_Not_a_wp_implication : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not_a_wp_implication (uu____12) -> begin
true
end
| uu____15 -> begin
false
end))


let __proj__Not_a_wp_implication__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Not_a_wp_implication (uu____25) -> begin
uu____25
end))


type label =
FStar_SMTEncoding_Term.error_label


type labels =
FStar_SMTEncoding_Term.error_labels


let sort_labels : (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list  ->  ((FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) * Prims.bool) Prims.list = (fun l -> (FStar_List.sortWith (fun uu____83 uu____84 -> (match (((uu____83), (uu____84))) with
| (((uu____134, uu____135, r1), uu____137), ((uu____138, uu____139, r2), uu____141)) -> begin
(FStar_Range.compare r1 r2)
end)) l))


let remove_dups : labels  ->  (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_Util.remove_dups (fun uu____218 uu____219 -> (match (((uu____218), (uu____219))) with
| ((uu____249, m1, r1), (uu____252, m2, r2)) -> begin
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

let uu____319 = (

let uu____321 = (FStar_ST.op_Bang ctr)
in (FStar_Util.string_of_int uu____321))
in (FStar_Util.format1 "label_%s" uu____319));
)
in (

let lvar = (FStar_SMTEncoding_Term.mk_fv ((l), (FStar_SMTEncoding_Term.Bool_sort)))
in (

let label = ((lvar), (message), (range))
in (

let lterm = (FStar_SMTEncoding_Util.mkFreeV lvar)
in (

let lt1 = (FStar_SMTEncoding_Term.mkOr ((lterm), (t)) range)
in ((label), (lt1)))))))))


let label_goals : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  FStar_SMTEncoding_Term.term  ->  (labels * FStar_SMTEncoding_Term.term) = (fun use_env_msg r q -> (

let rec is_a_post_condition = (fun post_name_opt tm -> (match (((post_name_opt), (tm.FStar_SMTEncoding_Term.tm))) with
| (FStar_Pervasives_Native.None, uu____415) -> begin
false
end
| (FStar_Pervasives_Native.Some (nm), FStar_SMTEncoding_Term.FreeV (fv)) -> begin
(

let uu____436 = (FStar_SMTEncoding_Term.fv_name fv)
in (Prims.op_Equality nm uu____436))
end
| (uu____439, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Valid"), (tm1)::[])) -> begin
(is_a_post_condition post_name_opt tm1)
end
| (uu____450, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("ApplyTT"), (tm1)::uu____452)) -> begin
(is_a_post_condition post_name_opt tm1)
end
| uu____464 -> begin
false
end))
in (

let conjuncts = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> begin
cs
end
| uu____488 -> begin
(t)::[]
end))
in (

let is_guard_free = (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____498; FStar_SMTEncoding_Term.rng = uu____499})::[])::[], iopt, uu____501, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (l)::(r1)::[]); FStar_SMTEncoding_Term.freevars = uu____504; FStar_SMTEncoding_Term.rng = uu____505}, uu____506) -> begin
true
end
| uu____561 -> begin
false
end))
in (

let is_a_named_continuation = (fun lhs -> (FStar_All.pipe_right (conjuncts lhs) (FStar_Util.for_some is_guard_free)))
in (

let uu____573 = (match (use_env_msg) with
| FStar_Pervasives_Native.None -> begin
((false), (""))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____603 = (f ())
in ((true), (uu____603)))
end)
in (match (uu____573) with
| (flag, msg_prefix) -> begin
(

let fresh_label1 = (fun msg ropt rng t -> (

let msg1 = (match (flag) with
| true -> begin
(Prims.op_Hat "Failed to verify implicit argument: " (Prims.op_Hat msg_prefix (Prims.op_Hat " :: " msg)))
end
| uu____655 -> begin
msg
end)
in (

let rng1 = (match (ropt) with
| FStar_Pervasives_Native.None -> begin
rng
end
| FStar_Pervasives_Native.Some (r1) -> begin
(

let uu____659 = (

let uu____661 = (FStar_Range.use_range rng)
in (

let uu____662 = (FStar_Range.use_range r1)
in (FStar_Range.rng_included uu____661 uu____662)))
in (match (uu____659) with
| true -> begin
rng
end
| uu____664 -> begin
(

let uu____666 = (FStar_Range.def_range rng)
in (FStar_Range.set_def_range r1 uu____666))
end))
end)
in (fresh_label msg1 rng1 t))))
in (

let rec aux = (fun default_msg ropt post_name_opt labels q1 -> (match (q1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.BoundV (uu____721) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.Integer (uu____725) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.Real (uu____729) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.LblPos (uu____733) -> begin
(failwith "Impossible")
end
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", uu____747) -> begin
(

let fallback = (fun msg -> (aux default_msg ropt post_name_opt labels arg))
in (FStar_All.try_with (fun uu___143_794 -> (match (()) with
| () -> begin
(match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, (post)::sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____813; FStar_SMTEncoding_Term.rng = rng}, uu____815) -> begin
(

let post_name = (

let uu____856 = (

let uu____858 = (FStar_Ident.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____858))
in (Prims.op_Hat "^^post_condition_" uu____856))
in (

let names1 = (

let uu____866 = (FStar_SMTEncoding_Term.mk_fv ((post_name), (post)))
in (

let uu____868 = (FStar_List.map (fun s -> (

let uu____874 = (

let uu____880 = (

let uu____882 = (

let uu____884 = (FStar_Ident.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____884))
in (Prims.op_Hat "^^" uu____882))
in ((uu____880), (s)))
in (FStar_SMTEncoding_Term.mk_fv uu____874))) sorts)
in (uu____866)::uu____868))
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1)
in (

let uu____893 = (

let uu____898 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____899 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____898), (uu____899))))
in (match (uu____893) with
| (lhs1, rhs1) -> begin
(

let uu____908 = (match (lhs1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, clauses_lhs) -> begin
(

let uu____926 = (FStar_Util.prefix clauses_lhs)
in (match (uu____926) with
| (req, ens) -> begin
(match (ens.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats_ens, iopt_ens, sorts_ens, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (ensures_conjuncts)::(post1)::[]); FStar_SMTEncoding_Term.freevars = uu____956; FStar_SMTEncoding_Term.rng = rng_ens}, uu____958) -> begin
(

let uu____997 = (is_a_post_condition (FStar_Pervasives_Native.Some (post_name)) post1)
in (match (uu____997) with
| true -> begin
(

let uu____1007 = (aux "could not prove post-condition" FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels ensures_conjuncts)
in (match (uu____1007) with
| (labels1, ensures_conjuncts1) -> begin
(

let pats_ens1 = (match (pats_ens) with
| [] -> begin
((post1)::[])::[]
end
| ([])::[] -> begin
((post1)::[])::[]
end
| uu____1051 -> begin
pats_ens
end)
in (

let ens1 = (

let uu____1057 = (

let uu____1058 = (

let uu____1083 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((ensures_conjuncts1)::(post1)::[])))) rng_ens)
in (

let uu____1086 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((FStar_SMTEncoding_Term.Forall), (pats_ens1), (iopt_ens), (sorts_ens), (uu____1083), (uu____1086))))
in FStar_SMTEncoding_Term.Quant (uu____1058))
in (FStar_SMTEncoding_Term.mk uu____1057 ens.FStar_SMTEncoding_Term.rng))
in (

let lhs2 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.And), ((FStar_List.append req ((ens1)::[])))))) lhs1.FStar_SMTEncoding_Term.rng)
in (

let uu____1109 = (FStar_SMTEncoding_Term.abstr names1 lhs2)
in ((labels1), (uu____1109))))))
end))
end
| uu____1112 -> begin
(

let uu____1114 = (

let uu____1115 = (

let uu____1117 = (

let uu____1119 = (

let uu____1121 = (FStar_SMTEncoding_Term.print_smt_term post1)
in (Prims.op_Hat "  ... " uu____1121))
in (Prims.op_Hat post_name uu____1119))
in (Prims.op_Hat "Ensures clause doesn\'t match post name:  " uu____1117))
in Not_a_wp_implication (uu____1115))
in (FStar_Exn.raise uu____1114))
end))
end
| uu____1131 -> begin
(

let uu____1132 = (

let uu____1133 = (

let uu____1135 = (

let uu____1137 = (

let uu____1139 = (FStar_SMTEncoding_Term.print_smt_term ens)
in (Prims.op_Hat "  ... " uu____1139))
in (Prims.op_Hat post_name uu____1137))
in (Prims.op_Hat "Ensures clause doesn\'t have the expected shape for post-condition " uu____1135))
in Not_a_wp_implication (uu____1133))
in (FStar_Exn.raise uu____1132))
end)
end))
end
| uu____1149 -> begin
(

let uu____1150 = (

let uu____1151 = (

let uu____1153 = (FStar_SMTEncoding_Term.print_smt_term lhs1)
in (Prims.op_Hat "LHS not a conjunct: " uu____1153))
in Not_a_wp_implication (uu____1151))
in (FStar_Exn.raise uu____1150))
end)
in (match (uu____908) with
| (labels1, lhs2) -> begin
(

let uu____1174 = (

let uu____1181 = (aux default_msg FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels1 rhs1)
in (match (uu____1181) with
| (labels2, rhs2) -> begin
(

let uu____1201 = (FStar_SMTEncoding_Term.abstr names1 rhs2)
in ((labels2), (uu____1201)))
end))
in (match (uu____1174) with
| (labels2, rhs2) -> begin
(

let body = (FStar_SMTEncoding_Term.mkImp ((lhs2), (rhs2)) rng)
in (

let uu____1217 = (

let uu____1218 = (

let uu____1219 = (

let uu____1244 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((FStar_SMTEncoding_Term.Forall), (pats), (iopt), ((post)::sorts), (body), (uu____1244)))
in FStar_SMTEncoding_Term.Quant (uu____1219))
in (FStar_SMTEncoding_Term.mk uu____1218 q1.FStar_SMTEncoding_Term.rng))
in ((labels2), (uu____1217))))
end))
end))
end)))))
end
| uu____1266 -> begin
(

let uu____1267 = (

let uu____1269 = (FStar_SMTEncoding_Term.print_smt_term arg)
in (Prims.op_Hat "arg not a quant: " uu____1269))
in (fallback uu____1267))
end)
end)) (fun uu___142_1274 -> (match (uu___142_1274) with
| Not_a_wp_implication (msg) -> begin
(fallback msg)
end))))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r1) -> begin
(aux reason (FStar_Pervasives_Native.Some (r1)) post_name_opt labels arg)
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, [], FStar_Pervasives_Native.None, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____1291; FStar_SMTEncoding_Term.rng = rng}, uu____1293) when (is_a_named_continuation lhs) -> begin
(

let uu____1328 = (FStar_Util.prefix sorts)
in (match (uu____1328) with
| (sorts', post) -> begin
(

let new_post_name = (

let uu____1349 = (

let uu____1351 = (FStar_Ident.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____1351))
in (Prims.op_Hat "^^post_condition_" uu____1349))
in (

let names1 = (

let uu____1359 = (FStar_List.map (fun s -> (

let uu____1365 = (

let uu____1371 = (

let uu____1373 = (

let uu____1375 = (FStar_Ident.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____1375))
in (Prims.op_Hat "^^" uu____1373))
in ((uu____1371), (s)))
in (FStar_SMTEncoding_Term.mk_fv uu____1365))) sorts')
in (

let uu____1381 = (

let uu____1384 = (FStar_SMTEncoding_Term.mk_fv ((new_post_name), (post)))
in (uu____1384)::[])
in (FStar_List.append uu____1359 uu____1381)))
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1)
in (

let uu____1389 = (

let uu____1394 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____1395 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____1394), (uu____1395))))
in (match (uu____1389) with
| (lhs1, rhs1) -> begin
(

let uu____1404 = (FStar_Util.fold_map (fun labels1 tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____1443; FStar_SMTEncoding_Term.rng = uu____1444})::[])::[], iopt, sorts1, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (l0)::(r1)::[]); FStar_SMTEncoding_Term.freevars = uu____1449; FStar_SMTEncoding_Term.rng = uu____1450}, uu____1451) -> begin
(

let uu____1505 = (is_a_post_condition (FStar_Pervasives_Native.Some (new_post_name)) r1)
in (match (uu____1505) with
| true -> begin
(

let uu____1515 = (aux default_msg FStar_Pervasives_Native.None post_name_opt labels1 l0)
in (match (uu____1515) with
| (labels2, l) -> begin
(

let uu____1534 = (

let uu____1535 = (

let uu____1536 = (

let uu____1561 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((l)::(r1)::[])))))
in (

let uu____1564 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), (sorts1), (uu____1561), (uu____1564))))
in FStar_SMTEncoding_Term.Quant (uu____1536))
in (FStar_SMTEncoding_Term.mk uu____1535 q1.FStar_SMTEncoding_Term.rng))
in ((labels2), (uu____1534)))
end))
end
| uu____1592 -> begin
((labels1), (tm))
end))
end
| uu____1596 -> begin
((labels1), (tm))
end)) labels (conjuncts lhs1))
in (match (uu____1404) with
| (labels1, lhs_conjs) -> begin
(

let uu____1615 = (aux default_msg FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (new_post_name)) labels1 rhs1)
in (match (uu____1615) with
| (labels2, rhs2) -> begin
(

let body = (

let uu____1636 = (

let uu____1637 = (

let uu____1642 = (FStar_SMTEncoding_Term.mk_and_l lhs_conjs lhs1.FStar_SMTEncoding_Term.rng)
in ((uu____1642), (rhs2)))
in (FStar_SMTEncoding_Term.mkImp uu____1637 rng))
in (FStar_All.pipe_right uu____1636 (FStar_SMTEncoding_Term.abstr names1)))
in (

let q2 = (

let uu____1644 = (

let uu____1645 = (

let uu____1670 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((FStar_SMTEncoding_Term.Forall), ([]), (FStar_Pervasives_Native.None), (sorts), (body), (uu____1670)))
in FStar_SMTEncoding_Term.Quant (uu____1645))
in (FStar_SMTEncoding_Term.mk uu____1644 q1.FStar_SMTEncoding_Term.rng))
in ((labels2), (q2))))
end))
end))
end)))))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let uu____1699 = (aux default_msg ropt post_name_opt labels rhs)
in (match (uu____1699) with
| (labels1, rhs1) -> begin
(

let uu____1718 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs1)))
in ((labels1), (uu____1718)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts1) -> begin
(

let uu____1726 = (FStar_Util.fold_map (aux default_msg ropt post_name_opt) labels conjuncts1)
in (match (uu____1726) with
| (labels1, conjuncts2) -> begin
(

let uu____1753 = (FStar_SMTEncoding_Term.mk_and_l conjuncts2 q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____1753)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd1)::(q11)::(q2)::[]) -> begin
(

let uu____1761 = (aux default_msg ropt post_name_opt labels q11)
in (match (uu____1761) with
| (labels1, q12) -> begin
(

let uu____1780 = (aux default_msg ropt post_name_opt labels1 q2)
in (match (uu____1780) with
| (labels2, q21) -> begin
(

let uu____1799 = (FStar_SMTEncoding_Term.mkITE ((hd1), (q12), (q21)) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (uu____1799)))
end))
end))
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, uu____1802, uu____1803, uu____1804, uu____1805, uu____1806) -> begin
(

let uu____1831 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1831) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, uu____1846) -> begin
(

let uu____1851 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1851) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, uu____1866) -> begin
(

let uu____1871 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1871) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____1886), uu____1887) when (is_a_post_condition post_name_opt q1) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.FreeV (uu____1895) -> begin
(

let uu____1904 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1904) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____1919) -> begin
(

let uu____1924 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1924) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____1939) -> begin
(

let uu____1944 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1944) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, uu____1959) -> begin
(

let uu____1964 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1964) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, uu____1979) -> begin
(

let uu____1984 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1984) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, uu____1999) -> begin
(

let uu____2004 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2004) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, uu____2019) -> begin
(

let uu____2024 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2024) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, uu____2039) -> begin
(

let uu____2044 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2044) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, uu____2059) -> begin
(

let uu____2064 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2064) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUlt, uu____2079) -> begin
(

let uu____2084 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2084) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____2099), uu____2100) -> begin
(

let uu____2106 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____2106) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.RealDiv, uu____2121) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Add, uu____2133) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Sub, uu____2145) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Div, uu____2157) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mul, uu____2169) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Minus, uu____2181) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mod, uu____2193) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvAnd, uu____2205) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvXor, uu____2217) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvOr, uu____2229) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvAdd, uu____2241) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvSub, uu____2253) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvShl, uu____2265) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvShr, uu____2277) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUdiv, uu____2289) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvMod, uu____2301) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvMul, uu____2313) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUext (uu____2325), uu____2326) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvToNat, uu____2339) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.NatToBv (uu____2351), uu____2352) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, uu____2365) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, uu____2377) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body, uu____2393) -> begin
(

let uu____2418 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____2418) with
| (labels1, body1) -> begin
(

let uu____2437 = (

let uu____2438 = (

let uu____2439 = (

let uu____2464 = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body1), (uu____2464)))
in FStar_SMTEncoding_Term.Quant (uu____2439))
in (FStar_SMTEncoding_Term.mk uu____2438 q1.FStar_SMTEncoding_Term.rng))
in ((labels1), (uu____2437)))
end))
end
| FStar_SMTEncoding_Term.Let (es, body) -> begin
(

let uu____2492 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____2492) with
| (labels1, body1) -> begin
(

let uu____2511 = (FStar_SMTEncoding_Term.mkLet ((es), (body1)) q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____2511)))
end))
end))
in (aux "assertion failed" FStar_Pervasives_Native.None FStar_Pervasives_Native.None [] q)))
end)))))))


let detail_errors : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  labels  ->  (FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Z3.z3result)  ->  unit = (fun hint_replay env all_labels askZ3 -> (

let print_banner = (fun uu____2555 -> (

let msg = (

let uu____2558 = (

let uu____2560 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____2560))
in (

let uu____2561 = (FStar_Util.string_of_int (Prims.parse_int "5"))
in (

let uu____2564 = (FStar_Util.string_of_int (FStar_List.length all_labels))
in (FStar_Util.format4 "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n" (match (hint_replay) with
| true -> begin
"hint replay"
end
| uu____2570 -> begin
"error"
end) uu____2558 uu____2561 uu____2564))))
in (FStar_Util.print_error msg)))
in (

let print_result = (fun uu____2590 -> (match (uu____2590) with
| ((uu____2603, msg, r), success) -> begin
(match (success) with
| true -> begin
(

let uu____2619 = (FStar_Range.string_of_range r)
in (FStar_Util.print1 "OK: proof obligation at %s was proven in isolation\n" uu____2619))
end
| uu____2622 -> begin
(match (hint_replay) with
| true -> begin
(FStar_Errors.log_issue r ((FStar_Errors.Warning_HintFailedToReplayProof), ((Prims.op_Hat "Hint failed to replay this sub-proof: " msg))))
end
| uu____2627 -> begin
(

let uu____2629 = (

let uu____2635 = (

let uu____2637 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "XX: proof obligation at %s failed\n\t%s\n" uu____2637 msg))
in ((FStar_Errors.Error_ProofObligationFailed), (uu____2635)))
in (FStar_Errors.log_issue r uu____2629))
end)
end)
end))
in (

let elim = (fun labs -> (FStar_All.pipe_right labs (FStar_List.map (fun uu____2690 -> (match (uu____2690) with
| (l, uu____2699, uu____2700) -> begin
(

let a = (

let uu____2704 = (

let uu____2705 = (

let uu____2710 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((uu____2710), (FStar_SMTEncoding_Util.mkTrue)))
in (FStar_SMTEncoding_Util.mkEq uu____2705))
in (

let uu____2711 = (

let uu____2713 = (FStar_SMTEncoding_Term.fv_name l)
in (Prims.op_Hat "@disable_label_" uu____2713))
in {FStar_SMTEncoding_Term.assumption_term = uu____2704; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("Disabling label"); FStar_SMTEncoding_Term.assumption_name = uu____2711; FStar_SMTEncoding_Term.assumption_fact_ids = []}))
in FStar_SMTEncoding_Term.Assume (a))
end)))))
in (

let rec linear_check = (fun eliminated errors active -> ((FStar_SMTEncoding_Z3.refresh ());
(match (active) with
| [] -> begin
(

let results = (

let uu____2783 = (FStar_List.map (fun x -> ((x), (true))) eliminated)
in (

let uu____2800 = (FStar_List.map (fun x -> ((x), (false))) errors)
in (FStar_List.append uu____2783 uu____2800)))
in (sort_labels results))
end
| (hd1)::tl1 -> begin
((

let uu____2827 = (FStar_Util.string_of_int (FStar_List.length active))
in (FStar_Util.print1 "%s, " uu____2827));
(

let decls = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl1)))
in (

let result = (askZ3 decls)
in (match (result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____2859) -> begin
(linear_check ((hd1)::eliminated) errors tl1)
end
| uu____2860 -> begin
(linear_check eliminated ((hd1)::errors) tl1)
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
(

let uu____2909 = (FStar_Util.for_all FStar_Pervasives_Native.snd res)
in (match (uu____2909) with
| true -> begin
(FStar_Util.print_string "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n")
end
| uu____2933 -> begin
()
end));
));
))))))






open Prims
open FStar_Pervasives
exception Not_a_wp_implication of (Prims.string)


let uu___is_Not_a_wp_implication : Prims.exn  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Not_a_wp_implication (uu____10) -> begin
true
end
| uu____11 -> begin
false
end))


let __proj__Not_a_wp_implication__item__uu___ : Prims.exn  ->  Prims.string = (fun projectee -> (match (projectee) with
| Not_a_wp_implication (uu____18) -> begin
uu____18
end))


type label =
FStar_SMTEncoding_Term.error_label


type labels =
FStar_SMTEncoding_Term.error_labels


let sort_labels : (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list  ->  ((FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) * Prims.bool) Prims.list = (fun l -> (FStar_List.sortWith (fun uu____68 uu____69 -> (match (((uu____68), (uu____69))) with
| (((uu____110, uu____111, r1), uu____113), ((uu____114, uu____115, r2), uu____117)) -> begin
(FStar_Range.compare r1 r2)
end)) l))


let remove_dups : labels  ->  (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_Util.remove_dups (fun uu____177 uu____178 -> (match (((uu____177), (uu____178))) with
| ((uu____203, m1, r1), (uu____206, m2, r2)) -> begin
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

let uu____290 = (

let uu____291 = (FStar_ST.op_Bang ctr)
in (FStar_Util.string_of_int uu____291))
in (FStar_Util.format1 "label_%s" uu____290));
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


let label_goals : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_Range.range  ->  FStar_SMTEncoding_Term.term  ->  (labels * FStar_SMTEncoding_Term.term) = (fun use_env_msg r q -> (

let rec is_a_post_condition = (fun post_name_opt tm -> (match (((post_name_opt), (tm.FStar_SMTEncoding_Term.tm))) with
| (FStar_Pervasives_Native.None, uu____396) -> begin
false
end
| (FStar_Pervasives_Native.Some (nm), FStar_SMTEncoding_Term.FreeV (nm', uu____401)) -> begin
(Prims.op_Equality nm nm')
end
| (uu____404, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Valid"), (tm1)::[])) -> begin
(is_a_post_condition post_name_opt tm1)
end
| (uu____412, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("ApplyTT"), (tm1)::uu____414)) -> begin
(is_a_post_condition post_name_opt tm1)
end
| uu____423 -> begin
false
end))
in (

let conjuncts = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> begin
cs
end
| uu____445 -> begin
(t)::[]
end))
in (

let is_guard_free = (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____453; FStar_SMTEncoding_Term.rng = uu____454})::[])::[], iopt, uu____456, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (l)::(r1)::[]); FStar_SMTEncoding_Term.freevars = uu____459; FStar_SMTEncoding_Term.rng = uu____460}) -> begin
true
end
| uu____497 -> begin
false
end))
in (

let is_a_named_continuation = (fun lhs -> (FStar_All.pipe_right (conjuncts lhs) (FStar_Util.for_some is_guard_free)))
in (

let uu____506 = (match (use_env_msg) with
| FStar_Pervasives_Native.None -> begin
((false), (""))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____525 = (f ())
in ((true), (uu____525)))
end)
in (match (uu____506) with
| (flag, msg_prefix) -> begin
(

let fresh_label1 = (fun msg ropt rng t -> (

let msg1 = (match (flag) with
| true -> begin
(Prims.strcat "Failed to verify implicit argument: " (Prims.strcat msg_prefix (Prims.strcat " :: " msg)))
end
| uu____562 -> begin
msg
end)
in (

let rng1 = (match (ropt) with
| FStar_Pervasives_Native.None -> begin
rng
end
| FStar_Pervasives_Native.Some (r1) -> begin
(

let uu____565 = (

let uu____566 = (FStar_Range.use_range rng)
in (

let uu____567 = (FStar_Range.use_range r1)
in (FStar_Range.rng_included uu____566 uu____567)))
in (match (uu____565) with
| true -> begin
rng
end
| uu____568 -> begin
(

let uu____569 = (FStar_Range.def_range rng)
in (FStar_Range.set_def_range r1 uu____569))
end))
end)
in (fresh_label msg1 rng1 t))))
in (

let rec aux = (fun default_msg ropt post_name_opt labels q1 -> (match (q1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.BoundV (uu____620) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.Integer (uu____623) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.LblPos (uu____626) -> begin
(failwith "Impossible")
end
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", uu____638) -> begin
(

let fallback = (fun msg -> (aux default_msg ropt post_name_opt labels arg))
in (FStar_All.try_with (fun uu___272_680 -> (match (()) with
| () -> begin
(match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, (post)::sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____699; FStar_SMTEncoding_Term.rng = rng}) -> begin
(

let post_name = (

let uu____728 = (

let uu____729 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____729))
in (Prims.strcat "^^post_condition_" uu____728))
in (

let names1 = (

let uu____737 = (FStar_List.map (fun s -> (

let uu____751 = (

let uu____752 = (

let uu____753 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____753))
in (Prims.strcat "^^" uu____752))
in ((uu____751), (s)))) sorts)
in (((post_name), (post)))::uu____737)
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1)
in (

let uu____765 = (

let uu____770 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____771 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____770), (uu____771))))
in (match (uu____765) with
| (lhs1, rhs1) -> begin
(

let uu____780 = (match (lhs1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, clauses_lhs) -> begin
(

let uu____798 = (FStar_Util.prefix clauses_lhs)
in (match (uu____798) with
| (req, ens) -> begin
(match (ens.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats_ens, iopt_ens, sorts_ens, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (ensures_conjuncts)::(post1)::[]); FStar_SMTEncoding_Term.freevars = uu____828; FStar_SMTEncoding_Term.rng = rng_ens}) -> begin
(

let uu____856 = (is_a_post_condition (FStar_Pervasives_Native.Some (post_name)) post1)
in (match (uu____856) with
| true -> begin
(

let uu____863 = (aux "could not prove post-condition" FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels ensures_conjuncts)
in (match (uu____863) with
| (labels1, ensures_conjuncts1) -> begin
(

let pats_ens1 = (match (pats_ens) with
| [] -> begin
((post1)::[])::[]
end
| ([])::[] -> begin
((post1)::[])::[]
end
| uu____905 -> begin
pats_ens
end)
in (

let ens1 = (

let uu____911 = (

let uu____912 = (

let uu____931 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((ensures_conjuncts1)::(post1)::[])))) rng_ens)
in ((FStar_SMTEncoding_Term.Forall), (pats_ens1), (iopt_ens), (sorts_ens), (uu____931)))
in FStar_SMTEncoding_Term.Quant (uu____912))
in (FStar_SMTEncoding_Term.mk uu____911 ens.FStar_SMTEncoding_Term.rng))
in (

let lhs2 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.And), ((FStar_List.append req ((ens1)::[])))))) lhs1.FStar_SMTEncoding_Term.rng)
in (

let uu____945 = (FStar_SMTEncoding_Term.abstr names1 lhs2)
in ((labels1), (uu____945))))))
end))
end
| uu____948 -> begin
(

let uu____949 = (

let uu____950 = (

let uu____951 = (

let uu____952 = (

let uu____953 = (FStar_SMTEncoding_Term.print_smt_term post1)
in (Prims.strcat "  ... " uu____953))
in (Prims.strcat post_name uu____952))
in (Prims.strcat "Ensures clause doesn\'t match post name:  " uu____951))
in Not_a_wp_implication (uu____950))
in (FStar_Exn.raise uu____949))
end))
end
| uu____960 -> begin
(

let uu____961 = (

let uu____962 = (

let uu____963 = (

let uu____964 = (

let uu____965 = (FStar_SMTEncoding_Term.print_smt_term ens)
in (Prims.strcat "  ... " uu____965))
in (Prims.strcat post_name uu____964))
in (Prims.strcat "Ensures clause doesn\'t have the expected shape for post-condition " uu____963))
in Not_a_wp_implication (uu____962))
in (FStar_Exn.raise uu____961))
end)
end))
end
| uu____972 -> begin
(

let uu____973 = (

let uu____974 = (

let uu____975 = (FStar_SMTEncoding_Term.print_smt_term lhs1)
in (Prims.strcat "LHS not a conjunct: " uu____975))
in Not_a_wp_implication (uu____974))
in (FStar_Exn.raise uu____973))
end)
in (match (uu____780) with
| (labels1, lhs2) -> begin
(

let uu____994 = (

let uu____1001 = (aux default_msg FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels1 rhs1)
in (match (uu____1001) with
| (labels2, rhs2) -> begin
(

let uu____1020 = (FStar_SMTEncoding_Term.abstr names1 rhs2)
in ((labels2), (uu____1020)))
end))
in (match (uu____994) with
| (labels2, rhs2) -> begin
(

let body = (FStar_SMTEncoding_Term.mkImp ((lhs2), (rhs2)) rng)
in (

let uu____1036 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), ((post)::sorts), (body)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (uu____1036))))
end))
end))
end)))))
end
| uu____1047 -> begin
(

let uu____1048 = (

let uu____1049 = (FStar_SMTEncoding_Term.print_smt_term arg)
in (Prims.strcat "arg not a quant: " uu____1049))
in (fallback uu____1048))
end)
end)) (fun uu___271_1052 -> (match (uu___271_1052) with
| Not_a_wp_implication (msg) -> begin
(fallback msg)
end))))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r1) -> begin
(aux reason (FStar_Pervasives_Native.Some (r1)) post_name_opt labels arg)
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, [], FStar_Pervasives_Native.None, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____1066; FStar_SMTEncoding_Term.rng = rng}) when (is_a_named_continuation lhs) -> begin
(

let uu____1090 = (FStar_Util.prefix sorts)
in (match (uu____1090) with
| (sorts', post) -> begin
(

let new_post_name = (

let uu____1110 = (

let uu____1111 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____1111))
in (Prims.strcat "^^post_condition_" uu____1110))
in (

let names1 = (

let uu____1119 = (FStar_List.map (fun s -> (

let uu____1133 = (

let uu____1134 = (

let uu____1135 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____1135))
in (Prims.strcat "^^" uu____1134))
in ((uu____1133), (s)))) sorts')
in (FStar_List.append uu____1119 ((((new_post_name), (post)))::[])))
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1)
in (

let uu____1155 = (

let uu____1160 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____1161 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____1160), (uu____1161))))
in (match (uu____1155) with
| (lhs1, rhs1) -> begin
(

let uu____1170 = (FStar_Util.fold_map (fun labels1 tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____1208; FStar_SMTEncoding_Term.rng = uu____1209})::[])::[], iopt, sorts1, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (l0)::(r1)::[]); FStar_SMTEncoding_Term.freevars = uu____1214; FStar_SMTEncoding_Term.rng = uu____1215}) -> begin
(

let uu____1252 = (is_a_post_condition (FStar_Pervasives_Native.Some (new_post_name)) r1)
in (match (uu____1252) with
| true -> begin
(

let uu____1259 = (aux default_msg FStar_Pervasives_Native.None post_name_opt labels1 l0)
in (match (uu____1259) with
| (labels2, l) -> begin
(

let uu____1278 = (

let uu____1279 = (

let uu____1280 = (

let uu____1299 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((l)::(r1)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), (sorts1), (uu____1299)))
in FStar_SMTEncoding_Term.Quant (uu____1280))
in (FStar_SMTEncoding_Term.mk uu____1279 q1.FStar_SMTEncoding_Term.rng))
in ((labels2), (uu____1278)))
end))
end
| uu____1316 -> begin
((labels1), (tm))
end))
end
| uu____1319 -> begin
((labels1), (tm))
end)) labels (conjuncts lhs1))
in (match (uu____1170) with
| (labels1, lhs_conjs) -> begin
(

let uu____1338 = (aux default_msg FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (new_post_name)) labels1 rhs1)
in (match (uu____1338) with
| (labels2, rhs2) -> begin
(

let body = (

let uu____1358 = (

let uu____1359 = (

let uu____1364 = (FStar_SMTEncoding_Term.mk_and_l lhs_conjs lhs1.FStar_SMTEncoding_Term.rng)
in ((uu____1364), (rhs2)))
in (FStar_SMTEncoding_Term.mkImp uu____1359 rng))
in (FStar_All.pipe_right uu____1358 (FStar_SMTEncoding_Term.abstr names1)))
in (

let q2 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), ([]), (FStar_Pervasives_Native.None), (sorts), (body)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (q2))))
end))
end))
end)))))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let uu____1382 = (aux default_msg ropt post_name_opt labels rhs)
in (match (uu____1382) with
| (labels1, rhs1) -> begin
(

let uu____1401 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs1)))
in ((labels1), (uu____1401)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts1) -> begin
(

let uu____1409 = (FStar_Util.fold_map (aux default_msg ropt post_name_opt) labels conjuncts1)
in (match (uu____1409) with
| (labels1, conjuncts2) -> begin
(

let uu____1436 = (FStar_SMTEncoding_Term.mk_and_l conjuncts2 q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____1436)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd1)::(q11)::(q2)::[]) -> begin
(

let uu____1444 = (aux default_msg ropt post_name_opt labels q11)
in (match (uu____1444) with
| (labels1, q12) -> begin
(

let uu____1463 = (aux default_msg ropt post_name_opt labels1 q2)
in (match (uu____1463) with
| (labels2, q21) -> begin
(

let uu____1482 = (FStar_SMTEncoding_Term.mkITE ((hd1), (q12), (q21)) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (uu____1482)))
end))
end))
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, uu____1485, uu____1486, uu____1487, uu____1488) -> begin
(

let uu____1505 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1505) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, uu____1520) -> begin
(

let uu____1525 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1525) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, uu____1540) -> begin
(

let uu____1545 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1545) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____1560), uu____1561) when (is_a_post_condition post_name_opt q1) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.FreeV (uu____1568) -> begin
(

let uu____1573 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1573) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____1588) -> begin
(

let uu____1593 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1593) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____1608) -> begin
(

let uu____1613 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1613) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, uu____1628) -> begin
(

let uu____1633 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1633) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, uu____1648) -> begin
(

let uu____1653 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1653) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, uu____1668) -> begin
(

let uu____1673 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1673) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, uu____1688) -> begin
(

let uu____1693 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1693) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, uu____1708) -> begin
(

let uu____1713 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1713) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, uu____1728) -> begin
(

let uu____1733 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1733) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUlt, uu____1748) -> begin
(

let uu____1753 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1753) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____1768), uu____1769) -> begin
(

let uu____1774 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1774) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Add, uu____1789) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Sub, uu____1800) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Div, uu____1811) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mul, uu____1822) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Minus, uu____1833) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mod, uu____1844) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvAnd, uu____1855) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvXor, uu____1866) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvOr, uu____1877) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvAdd, uu____1888) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvSub, uu____1899) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvShl, uu____1910) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvShr, uu____1921) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUdiv, uu____1932) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvMod, uu____1943) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvMul, uu____1954) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUext (uu____1965), uu____1966) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvToNat, uu____1977) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.NatToBv (uu____1988), uu____1989) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, uu____2000) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, uu____2011) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body) -> begin
(

let uu____2042 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____2042) with
| (labels1, body1) -> begin
(

let uu____2061 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body1)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____2061)))
end))
end
| FStar_SMTEncoding_Term.Let (es, body) -> begin
(

let uu____2078 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____2078) with
| (labels1, body1) -> begin
(

let uu____2097 = (FStar_SMTEncoding_Term.mkLet ((es), (body1)) q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____2097)))
end))
end))
in (aux "assertion failed" FStar_Pervasives_Native.None FStar_Pervasives_Native.None [] q)))
end)))))))


let detail_errors : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  FStar_SMTEncoding_Z3.z3result)  ->  unit = (fun hint_replay env all_labels askZ3 -> (

let print_banner = (fun uu____2132 -> (

let msg = (

let uu____2134 = (

let uu____2135 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____2135))
in (

let uu____2136 = (FStar_Util.string_of_int (Prims.parse_int "5"))
in (

let uu____2137 = (FStar_Util.string_of_int (FStar_List.length all_labels))
in (FStar_Util.format4 "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n" (match (hint_replay) with
| true -> begin
"hint replay"
end
| uu____2138 -> begin
"error"
end) uu____2134 uu____2136 uu____2137))))
in (FStar_Util.print_error msg)))
in (

let print_result = (fun uu____2154 -> (match (uu____2154) with
| ((uu____2165, msg, r), success) -> begin
(match (success) with
| true -> begin
(

let uu____2175 = (FStar_Range.string_of_range r)
in (FStar_Util.print1 "OK: proof obligation at %s was proven in isolation\n" uu____2175))
end
| uu____2176 -> begin
(match (hint_replay) with
| true -> begin
(FStar_Errors.log_issue r ((FStar_Errors.Warning_HintFailedToReplayProof), ((Prims.strcat "Hint failed to replay this sub-proof: " msg))))
end
| uu____2177 -> begin
(

let uu____2178 = (

let uu____2183 = (

let uu____2184 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "XX: proof obligation at %s failed\n\t%s\n" uu____2184 msg))
in ((FStar_Errors.Error_ProofObligationFailed), (uu____2183)))
in (FStar_Errors.log_issue r uu____2178))
end)
end)
end))
in (

let elim = (fun labs -> (FStar_All.pipe_right labs (FStar_List.map (fun uu____2246 -> (match (uu____2246) with
| (l, uu____2258, uu____2259) -> begin
(

let a = (

let uu____2269 = (

let uu____2270 = (

let uu____2275 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((uu____2275), (FStar_SMTEncoding_Util.mkTrue)))
in (FStar_SMTEncoding_Util.mkEq uu____2270))
in {FStar_SMTEncoding_Term.assumption_term = uu____2269; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("Disabling label"); FStar_SMTEncoding_Term.assumption_name = (Prims.strcat "@disable_label_" (FStar_Pervasives_Native.fst l)); FStar_SMTEncoding_Term.assumption_fact_ids = []})
in FStar_SMTEncoding_Term.Assume (a))
end)))))
in (

let rec linear_check = (fun eliminated errors active -> ((FStar_SMTEncoding_Z3.refresh ());
(match (active) with
| [] -> begin
(

let results = (

let uu____2336 = (FStar_List.map (fun x -> ((x), (true))) eliminated)
in (

let uu____2349 = (FStar_List.map (fun x -> ((x), (false))) errors)
in (FStar_List.append uu____2336 uu____2349)))
in (sort_labels results))
end
| (hd1)::tl1 -> begin
((

let uu____2371 = (FStar_Util.string_of_int (FStar_List.length active))
in (FStar_Util.print1 "%s, " uu____2371));
(

let decls = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl1)))
in (

let result = (askZ3 decls)
in (match (result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____2398) -> begin
(linear_check ((hd1)::eliminated) errors tl1)
end
| uu____2399 -> begin
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

let uu____2439 = (FStar_Util.for_all FStar_Pervasives_Native.snd res)
in (match (uu____2439) with
| true -> begin
(FStar_Util.print_string "Failed: the heuristic of trying each proof in isolation failed to identify a precise error\n")
end
| uu____2456 -> begin
()
end));
));
))))))





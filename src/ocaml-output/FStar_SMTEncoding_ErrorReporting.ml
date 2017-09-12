
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
| (FStar_Pervasives_Native.None, uu____372) -> begin
false
end
| (FStar_Pervasives_Native.Some (nm), FStar_SMTEncoding_Term.FreeV (nm', uu____377)) -> begin
(nm = nm')
end
| (uu____380, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Valid"), (tm1)::[])) -> begin
(is_a_post_condition post_name_opt tm1)
end
| (uu____388, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("ApplyTT"), (tm1)::uu____390)) -> begin
(is_a_post_condition post_name_opt tm1)
end
| uu____399 -> begin
false
end))
in (

let conjuncts = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> begin
cs
end
| uu____419 -> begin
(t)::[]
end))
in (

let is_guard_free = (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____425; FStar_SMTEncoding_Term.rng = uu____426})::[])::[], iopt, uu____428, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r1)::[]); FStar_SMTEncoding_Term.freevars = uu____431; FStar_SMTEncoding_Term.rng = uu____432}) -> begin
true
end
| uu____469 -> begin
false
end))
in (

let is_a_named_continuation = (fun lhs -> (FStar_All.pipe_right (conjuncts lhs) (FStar_Util.for_some is_guard_free)))
in (

let uu____476 = (match (use_env_msg) with
| FStar_Pervasives_Native.None -> begin
((false), (""))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____492 = (f ())
in ((true), (uu____492)))
end)
in (match (uu____476) with
| (flag, msg_prefix) -> begin
(

let fresh_label1 = (fun msg ropt rng t -> (

let msg1 = (match (flag) with
| true -> begin
(Prims.strcat "Failed to verify implicit argument: " msg)
end
| uu____521 -> begin
msg
end)
in (

let rng1 = (match (ropt) with
| FStar_Pervasives_Native.None -> begin
rng
end
| FStar_Pervasives_Native.Some (r1) -> begin
(

let uu___107_524 = r1
in {FStar_Range.def_range = rng.FStar_Range.def_range; FStar_Range.use_range = uu___107_524.FStar_Range.use_range})
end)
in (fresh_label msg1 rng1 t))))
in (

let rec aux = (fun default_msg ropt post_name_opt labels q1 -> (match (q1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.BoundV (uu____565) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.Integer (uu____568) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.LblPos (uu____571) -> begin
(failwith "Impossible")
end
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", uu____583) -> begin
(

let fallback = (fun msg -> (aux default_msg ropt post_name_opt labels arg))
in try
(match (()) with
| () -> begin
(match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, (post)::sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____642; FStar_SMTEncoding_Term.rng = rng}) -> begin
(

let post_name = (

let uu____671 = (

let uu____672 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____672))
in (Prims.strcat "^^post_condition_" uu____671))
in (

let names1 = (

let uu____680 = (FStar_List.mapi (fun i s -> (

let uu____696 = (

let uu____697 = (FStar_Util.string_of_int i)
in (Prims.strcat "^^" uu____697))
in ((uu____696), (s)))) sorts)
in (((post_name), (post)))::uu____680)
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1)
in (

let uu____709 = (

let uu____714 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____715 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____714), (uu____715))))
in (match (uu____709) with
| (lhs1, rhs1) -> begin
(

let uu____724 = (match (lhs1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, clauses_lhs) -> begin
(

let uu____742 = (FStar_Util.prefix clauses_lhs)
in (match (uu____742) with
| (req, ens) -> begin
(match (ens.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats_ens, iopt_ens, sorts_ens, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (ensures_conjuncts)::(post1)::[]); FStar_SMTEncoding_Term.freevars = uu____772; FStar_SMTEncoding_Term.rng = rng_ens}) when (is_a_post_condition (FStar_Pervasives_Native.Some (post_name)) post1) -> begin
(

let uu____800 = (aux "could not prove post-condition" FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels ensures_conjuncts)
in (match (uu____800) with
| (labels1, ensures_conjuncts1) -> begin
(

let pats_ens1 = (match (pats_ens) with
| [] -> begin
((post1)::[])::[]
end
| ([])::[] -> begin
((post1)::[])::[]
end
| uu____842 -> begin
pats_ens
end)
in (

let ens1 = (

let uu____848 = (

let uu____849 = (

let uu____868 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((ensures_conjuncts1)::(post1)::[])))) rng_ens)
in ((FStar_SMTEncoding_Term.Forall), (pats_ens1), (iopt_ens), (sorts_ens), (uu____868)))
in FStar_SMTEncoding_Term.Quant (uu____849))
in (FStar_SMTEncoding_Term.mk uu____848 ens.FStar_SMTEncoding_Term.rng))
in (

let lhs2 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.And), ((FStar_List.append req ((ens1)::[])))))) lhs1.FStar_SMTEncoding_Term.rng)
in (

let uu____882 = (FStar_SMTEncoding_Term.abstr names1 lhs2)
in ((labels1), (uu____882))))))
end))
end
| uu____885 -> begin
(

let uu____886 = (

let uu____887 = (

let uu____888 = (

let uu____889 = (

let uu____890 = (FStar_SMTEncoding_Term.print_smt_term ens)
in (Prims.strcat "  ... " uu____890))
in (Prims.strcat post_name uu____889))
in (Prims.strcat "Ensures clause doesn\'t match post name:  " uu____888))
in Not_a_wp_implication (uu____887))
in (FStar_Exn.raise uu____886))
end)
end))
end
| uu____897 -> begin
(

let uu____898 = (

let uu____899 = (

let uu____900 = (FStar_SMTEncoding_Term.print_smt_term lhs1)
in (Prims.strcat "LHS not a conjunct: " uu____900))
in Not_a_wp_implication (uu____899))
in (FStar_Exn.raise uu____898))
end)
in (match (uu____724) with
| (labels1, lhs2) -> begin
(

let uu____919 = (

let uu____926 = (aux default_msg FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels1 rhs1)
in (match (uu____926) with
| (labels2, rhs2) -> begin
(

let uu____945 = (FStar_SMTEncoding_Term.abstr names1 rhs2)
in ((labels2), (uu____945)))
end))
in (match (uu____919) with
| (labels2, rhs2) -> begin
(

let body = (FStar_SMTEncoding_Term.mkImp ((lhs2), (rhs2)) rng)
in (

let uu____961 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), ((post)::sorts), (body)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (uu____961))))
end))
end))
end)))))
end
| uu____972 -> begin
(

let uu____973 = (

let uu____974 = (FStar_SMTEncoding_Term.print_smt_term arg)
in (Prims.strcat "arg not a quant: " uu____974))
in (fallback uu____973))
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
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, [], FStar_Pervasives_Native.None, (post)::[], {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____991; FStar_SMTEncoding_Term.rng = rng}) when (is_a_named_continuation lhs) -> begin
(

let post_name = (

let uu____1014 = (

let uu____1015 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____1015))
in (Prims.strcat "^^post_condition_" uu____1014))
in (

let names1 = ((post_name), (post))
in (

let instantiation = (

let uu____1024 = (FStar_SMTEncoding_Util.mkFreeV names1)
in (uu____1024)::[])
in (

let uu____1025 = (

let uu____1030 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____1031 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____1030), (uu____1031))))
in (match (uu____1025) with
| (lhs1, rhs1) -> begin
(

let uu____1040 = (FStar_Util.fold_map (fun labels1 tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____1077; FStar_SMTEncoding_Term.rng = uu____1078})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r1)::[]); FStar_SMTEncoding_Term.freevars = uu____1083; FStar_SMTEncoding_Term.rng = uu____1084}) -> begin
(

let uu____1121 = (aux default_msg FStar_Pervasives_Native.None post_name_opt labels1 r1)
in (match (uu____1121) with
| (labels2, r2) -> begin
(

let uu____1140 = (

let uu____1141 = (

let uu____1142 = (

let uu____1161 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Iff), ((l)::(r2)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), (sorts), (uu____1161)))
in FStar_SMTEncoding_Term.Quant (uu____1142))
in (FStar_SMTEncoding_Term.mk uu____1141 q1.FStar_SMTEncoding_Term.rng))
in ((labels2), (uu____1140)))
end))
end
| uu____1178 -> begin
((labels1), (tm))
end)) labels (conjuncts lhs1))
in (match (uu____1040) with
| (labels1, lhs_conjs) -> begin
(

let uu____1197 = (aux default_msg FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels1 rhs1)
in (match (uu____1197) with
| (labels2, rhs2) -> begin
(

let body = (

let uu____1217 = (

let uu____1218 = (

let uu____1223 = (FStar_SMTEncoding_Term.mk_and_l lhs_conjs lhs1.FStar_SMTEncoding_Term.rng)
in ((uu____1223), (rhs2)))
in (FStar_SMTEncoding_Term.mkImp uu____1218 rng))
in (FStar_All.pipe_right uu____1217 (FStar_SMTEncoding_Term.abstr ((names1)::[]))))
in (

let q2 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), ([]), (FStar_Pervasives_Native.None), ((post)::[]), (body)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (q2))))
end))
end))
end)))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let uu____1249 = (aux default_msg ropt post_name_opt labels rhs)
in (match (uu____1249) with
| (labels1, rhs1) -> begin
(

let uu____1268 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs1)))
in ((labels1), (uu____1268)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts1) -> begin
(

let uu____1276 = (FStar_Util.fold_map (aux default_msg ropt post_name_opt) labels conjuncts1)
in (match (uu____1276) with
| (labels1, conjuncts2) -> begin
(

let uu____1303 = (FStar_SMTEncoding_Term.mk_and_l conjuncts2 q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____1303)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd1)::(q11)::(q2)::[]) -> begin
(

let uu____1311 = (aux default_msg ropt post_name_opt labels q11)
in (match (uu____1311) with
| (labels1, q12) -> begin
(

let uu____1330 = (aux default_msg ropt post_name_opt labels1 q2)
in (match (uu____1330) with
| (labels2, q21) -> begin
(

let uu____1349 = (FStar_SMTEncoding_Term.mkITE ((hd1), (q12), (q21)) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (uu____1349)))
end))
end))
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, uu____1352, uu____1353, uu____1354, uu____1355) -> begin
(

let uu____1372 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1372) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, uu____1387) -> begin
(

let uu____1392 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1392) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, uu____1407) -> begin
(

let uu____1412 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1412) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____1427), uu____1428) when (is_a_post_condition post_name_opt q1) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.FreeV (uu____1435) -> begin
(

let uu____1440 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1440) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____1455) -> begin
(

let uu____1460 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1460) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____1475) -> begin
(

let uu____1480 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1480) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, uu____1495) -> begin
(

let uu____1500 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1500) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, uu____1515) -> begin
(

let uu____1520 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1520) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, uu____1535) -> begin
(

let uu____1540 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1540) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, uu____1555) -> begin
(

let uu____1560 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1560) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, uu____1575) -> begin
(

let uu____1580 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1580) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, uu____1595) -> begin
(

let uu____1600 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1600) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUlt, uu____1615) -> begin
(

let uu____1620 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1620) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____1635), uu____1636) -> begin
(

let uu____1641 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1641) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Add, uu____1656) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Sub, uu____1667) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Div, uu____1678) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mul, uu____1689) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Minus, uu____1700) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mod, uu____1711) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvAnd, uu____1722) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvXor, uu____1733) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvOr, uu____1744) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvShl, uu____1755) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvShr, uu____1766) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUdiv, uu____1777) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvMod, uu____1788) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvMul, uu____1799) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUext (uu____1810), uu____1811) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvToNat, uu____1822) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.NatToBv (uu____1833), uu____1834) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, uu____1845) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, uu____1856) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body) -> begin
(

let uu____1887 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____1887) with
| (labels1, body1) -> begin
(

let uu____1906 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body1)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____1906)))
end))
end
| FStar_SMTEncoding_Term.Let (es, body) -> begin
(

let uu____1923 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____1923) with
| (labels1, body1) -> begin
(

let uu____1942 = (FStar_SMTEncoding_Term.mkLet ((es), (body1)) q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____1942)))
end))
end))
in (aux "assertion failed" FStar_Pervasives_Native.None FStar_Pervasives_Native.None [] q)))
end)))))))


let detail_errors : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  FStar_SMTEncoding_Z3.z3result)  ->  Prims.unit = (fun hint_replay env all_labels askZ3 -> (

let print_banner = (fun uu____1971 -> (

let msg = (

let uu____1973 = (

let uu____1974 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____1974))
in (

let uu____1975 = (FStar_Util.string_of_int (Prims.parse_int "5"))
in (

let uu____1976 = (FStar_Util.string_of_int (FStar_List.length all_labels))
in (FStar_Util.format4 "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n" (match (hint_replay) with
| true -> begin
"hint replay"
end
| uu____1977 -> begin
"error"
end) uu____1973 uu____1975 uu____1976))))
in (FStar_Util.print_error msg)))
in (

let print_result = (fun uu____1991 -> (match (uu____1991) with
| ((uu____2002, msg, r), success) -> begin
(match (success) with
| true -> begin
(

let uu____2012 = (FStar_Range.string_of_range r)
in (FStar_Util.print1_error "OK: proof obligation at %s was proven\n" uu____2012))
end
| uu____2013 -> begin
(match (hint_replay) with
| true -> begin
(FStar_Errors.warn r (Prims.strcat "Hint failed to replay this sub-proof: " msg))
end
| uu____2014 -> begin
((

let uu____2016 = (FStar_Range.string_of_range r)
in (FStar_Util.print2_error "XX: proof obligation at %s failed\n\t%s\n" uu____2016 msg));
(FStar_Errors.err r msg);
)
end)
end)
end))
in (

let elim = (fun labs -> (FStar_All.pipe_right labs (FStar_List.map (fun uu____2076 -> (match (uu____2076) with
| (l, uu____2088, uu____2089) -> begin
(

let a = (

let uu____2099 = (

let uu____2100 = (

let uu____2105 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((uu____2105), (FStar_SMTEncoding_Util.mkTrue)))
in (FStar_SMTEncoding_Util.mkEq uu____2100))
in {FStar_SMTEncoding_Term.assumption_term = uu____2099; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("Disabling label"); FStar_SMTEncoding_Term.assumption_name = (Prims.strcat "@disable_label_" (FStar_Pervasives_Native.fst l)); FStar_SMTEncoding_Term.assumption_fact_ids = []})
in FStar_SMTEncoding_Term.Assume (a))
end)))))
in (

let rec linear_check = (fun eliminated errors active -> ((FStar_SMTEncoding_Z3.refresh ());
(match (active) with
| [] -> begin
(

let results = (

let uu____2160 = (FStar_List.map (fun x -> ((x), (true))) eliminated)
in (

let uu____2173 = (FStar_List.map (fun x -> ((x), (false))) errors)
in (FStar_List.append uu____2160 uu____2173)))
in (sort_labels results))
end
| (hd1)::tl1 -> begin
((

let uu____2195 = (FStar_Util.string_of_int (FStar_List.length active))
in (FStar_Util.print1 "%s, " uu____2195));
(

let decls = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl1)))
in (

let uu____2213 = (askZ3 decls)
in (match (uu____2213) with
| (result, uu____2227, uu____2228) -> begin
(match (result) with
| FStar_SMTEncoding_Z3.UNSAT (uu____2241) -> begin
(linear_check ((hd1)::eliminated) errors tl1)
end
| uu____2242 -> begin
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





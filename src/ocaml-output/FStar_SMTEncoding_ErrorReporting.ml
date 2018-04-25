
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

let uu____362 = (

let uu____363 = (FStar_ST.op_Bang ctr)
in (FStar_Util.string_of_int uu____363))
in (FStar_Util.format1 "label_%s" uu____362));
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
| (FStar_Pervasives_Native.None, uu____544) -> begin
false
end
| (FStar_Pervasives_Native.Some (nm), FStar_SMTEncoding_Term.FreeV (nm', uu____549)) -> begin
(Prims.op_Equality nm nm')
end
| (uu____552, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Valid"), (tm1)::[])) -> begin
(is_a_post_condition post_name_opt tm1)
end
| (uu____560, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("ApplyTT"), (tm1)::uu____562)) -> begin
(is_a_post_condition post_name_opt tm1)
end
| uu____571 -> begin
false
end))
in (

let conjuncts = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> begin
cs
end
| uu____593 -> begin
(t)::[]
end))
in (

let is_guard_free = (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____601; FStar_SMTEncoding_Term.rng = uu____602})::[])::[], iopt, uu____604, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r1)::[]); FStar_SMTEncoding_Term.freevars = uu____607; FStar_SMTEncoding_Term.rng = uu____608}) -> begin
true
end
| uu____645 -> begin
false
end))
in (

let is_a_named_continuation = (fun lhs -> (FStar_All.pipe_right (conjuncts lhs) (FStar_Util.for_some is_guard_free)))
in (

let uu____654 = (match (use_env_msg) with
| FStar_Pervasives_Native.None -> begin
((false), (""))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____673 = (f ())
in ((true), (uu____673)))
end)
in (match (uu____654) with
| (flag, msg_prefix) -> begin
(

let fresh_label1 = (fun msg ropt rng t -> (

let msg1 = (match (flag) with
| true -> begin
(Prims.strcat "Failed to verify implicit argument: " msg)
end
| uu____710 -> begin
msg
end)
in (

let rng1 = (match (ropt) with
| FStar_Pervasives_Native.None -> begin
rng
end
| FStar_Pervasives_Native.Some (r1) -> begin
(

let uu____713 = (FStar_Range.def_range rng)
in (FStar_Range.set_def_range r1 uu____713))
end)
in (fresh_label msg1 rng1 t))))
in (

let rec aux = (fun default_msg ropt post_name_opt labels q1 -> (match (q1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.BoundV (uu____764) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.Integer (uu____767) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.LblPos (uu____770) -> begin
(failwith "Impossible")
end
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", uu____782) -> begin
(

let fallback = (fun msg -> (aux default_msg ropt post_name_opt labels arg))
in (FStar_All.try_with (fun uu___57_824 -> (match (()) with
| () -> begin
(match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, (post)::sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____843; FStar_SMTEncoding_Term.rng = rng}) -> begin
(

let post_name = (

let uu____872 = (

let uu____873 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____873))
in (Prims.strcat "^^post_condition_" uu____872))
in (

let names1 = (

let uu____881 = (FStar_List.mapi (fun i s -> (

let uu____897 = (

let uu____898 = (FStar_Util.string_of_int i)
in (Prims.strcat "^^" uu____898))
in ((uu____897), (s)))) sorts)
in (((post_name), (post)))::uu____881)
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names1)
in (

let uu____910 = (

let uu____915 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____916 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____915), (uu____916))))
in (match (uu____910) with
| (lhs1, rhs1) -> begin
(

let uu____925 = (match (lhs1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, clauses_lhs) -> begin
(

let uu____943 = (FStar_Util.prefix clauses_lhs)
in (match (uu____943) with
| (req, ens) -> begin
(match (ens.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats_ens, iopt_ens, sorts_ens, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (ensures_conjuncts)::(post1)::[]); FStar_SMTEncoding_Term.freevars = uu____973; FStar_SMTEncoding_Term.rng = rng_ens}) when (is_a_post_condition (FStar_Pervasives_Native.Some (post_name)) post1) -> begin
(

let uu____1001 = (aux "could not prove post-condition" FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels ensures_conjuncts)
in (match (uu____1001) with
| (labels1, ensures_conjuncts1) -> begin
(

let pats_ens1 = (match (pats_ens) with
| [] -> begin
((post1)::[])::[]
end
| ([])::[] -> begin
((post1)::[])::[]
end
| uu____1043 -> begin
pats_ens
end)
in (

let ens1 = (

let uu____1049 = (

let uu____1050 = (

let uu____1069 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((ensures_conjuncts1)::(post1)::[])))) rng_ens)
in ((FStar_SMTEncoding_Term.Forall), (pats_ens1), (iopt_ens), (sorts_ens), (uu____1069)))
in FStar_SMTEncoding_Term.Quant (uu____1050))
in (FStar_SMTEncoding_Term.mk uu____1049 ens.FStar_SMTEncoding_Term.rng))
in (

let lhs2 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.And), ((FStar_List.append req ((ens1)::[])))))) lhs1.FStar_SMTEncoding_Term.rng)
in (

let uu____1083 = (FStar_SMTEncoding_Term.abstr names1 lhs2)
in ((labels1), (uu____1083))))))
end))
end
| uu____1086 -> begin
(

let uu____1087 = (

let uu____1088 = (

let uu____1089 = (

let uu____1090 = (

let uu____1091 = (FStar_SMTEncoding_Term.print_smt_term ens)
in (Prims.strcat "  ... " uu____1091))
in (Prims.strcat post_name uu____1090))
in (Prims.strcat "Ensures clause doesn\'t match post name:  " uu____1089))
in Not_a_wp_implication (uu____1088))
in (FStar_Exn.raise uu____1087))
end)
end))
end
| uu____1098 -> begin
(

let uu____1099 = (

let uu____1100 = (

let uu____1101 = (FStar_SMTEncoding_Term.print_smt_term lhs1)
in (Prims.strcat "LHS not a conjunct: " uu____1101))
in Not_a_wp_implication (uu____1100))
in (FStar_Exn.raise uu____1099))
end)
in (match (uu____925) with
| (labels1, lhs2) -> begin
(

let uu____1120 = (

let uu____1127 = (aux default_msg FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels1 rhs1)
in (match (uu____1127) with
| (labels2, rhs2) -> begin
(

let uu____1146 = (FStar_SMTEncoding_Term.abstr names1 rhs2)
in ((labels2), (uu____1146)))
end))
in (match (uu____1120) with
| (labels2, rhs2) -> begin
(

let body = (FStar_SMTEncoding_Term.mkImp ((lhs2), (rhs2)) rng)
in (

let uu____1162 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), ((post)::sorts), (body)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (uu____1162))))
end))
end))
end)))))
end
| uu____1173 -> begin
(

let uu____1174 = (

let uu____1175 = (FStar_SMTEncoding_Term.print_smt_term arg)
in (Prims.strcat "arg not a quant: " uu____1175))
in (fallback uu____1174))
end)
end)) (fun uu___56_1178 -> (match (uu___56_1178) with
| Not_a_wp_implication (msg) -> begin
(fallback msg)
end))))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r1) -> begin
(aux reason (FStar_Pervasives_Native.Some (r1)) post_name_opt labels arg)
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, [], FStar_Pervasives_Native.None, (post)::[], {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = uu____1192; FStar_SMTEncoding_Term.rng = rng}) when (is_a_named_continuation lhs) -> begin
(

let post_name = (

let uu____1215 = (

let uu____1216 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int uu____1216))
in (Prims.strcat "^^post_condition_" uu____1215))
in (

let names1 = ((post_name), (post))
in (

let instantiation = (

let uu____1225 = (FStar_SMTEncoding_Util.mkFreeV names1)
in (uu____1225)::[])
in (

let uu____1226 = (

let uu____1231 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (

let uu____1232 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((uu____1231), (uu____1232))))
in (match (uu____1226) with
| (lhs1, rhs1) -> begin
(

let uu____1241 = (FStar_Util.fold_map (fun labels1 tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____1278; FStar_SMTEncoding_Term.rng = uu____1279})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r1)::[]); FStar_SMTEncoding_Term.freevars = uu____1284; FStar_SMTEncoding_Term.rng = uu____1285}) -> begin
(

let uu____1322 = (aux default_msg FStar_Pervasives_Native.None post_name_opt labels1 r1)
in (match (uu____1322) with
| (labels2, r2) -> begin
(

let uu____1341 = (

let uu____1342 = (

let uu____1343 = (

let uu____1362 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Iff), ((l)::(r2)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (FStar_Pervasives_Native.Some ((Prims.parse_int "0"))), (sorts), (uu____1362)))
in FStar_SMTEncoding_Term.Quant (uu____1343))
in (FStar_SMTEncoding_Term.mk uu____1342 q1.FStar_SMTEncoding_Term.rng))
in ((labels2), (uu____1341)))
end))
end
| uu____1379 -> begin
((labels1), (tm))
end)) labels (conjuncts lhs1))
in (match (uu____1241) with
| (labels1, lhs_conjs) -> begin
(

let uu____1398 = (aux default_msg FStar_Pervasives_Native.None (FStar_Pervasives_Native.Some (post_name)) labels1 rhs1)
in (match (uu____1398) with
| (labels2, rhs2) -> begin
(

let body = (

let uu____1418 = (

let uu____1419 = (

let uu____1424 = (FStar_SMTEncoding_Term.mk_and_l lhs_conjs lhs1.FStar_SMTEncoding_Term.rng)
in ((uu____1424), (rhs2)))
in (FStar_SMTEncoding_Term.mkImp uu____1419 rng))
in (FStar_All.pipe_right uu____1418 (FStar_SMTEncoding_Term.abstr ((names1)::[]))))
in (

let q2 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), ([]), (FStar_Pervasives_Native.None), ((post)::[]), (body)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (q2))))
end))
end))
end)))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let uu____1450 = (aux default_msg ropt post_name_opt labels rhs)
in (match (uu____1450) with
| (labels1, rhs1) -> begin
(

let uu____1469 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs1)))
in ((labels1), (uu____1469)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts1) -> begin
(

let uu____1477 = (FStar_Util.fold_map (aux default_msg ropt post_name_opt) labels conjuncts1)
in (match (uu____1477) with
| (labels1, conjuncts2) -> begin
(

let uu____1504 = (FStar_SMTEncoding_Term.mk_and_l conjuncts2 q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____1504)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd1)::(q11)::(q2)::[]) -> begin
(

let uu____1512 = (aux default_msg ropt post_name_opt labels q11)
in (match (uu____1512) with
| (labels1, q12) -> begin
(

let uu____1531 = (aux default_msg ropt post_name_opt labels1 q2)
in (match (uu____1531) with
| (labels2, q21) -> begin
(

let uu____1550 = (FStar_SMTEncoding_Term.mkITE ((hd1), (q12), (q21)) q1.FStar_SMTEncoding_Term.rng)
in ((labels2), (uu____1550)))
end))
end))
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, uu____1553, uu____1554, uu____1555, uu____1556) -> begin
(

let uu____1573 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1573) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, uu____1588) -> begin
(

let uu____1593 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1593) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, uu____1608) -> begin
(

let uu____1613 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1613) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____1628), uu____1629) when (is_a_post_condition post_name_opt q1) -> begin
((labels), (q1))
end
| FStar_SMTEncoding_Term.FreeV (uu____1636) -> begin
(

let uu____1641 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1641) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____1656) -> begin
(

let uu____1661 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1661) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____1676) -> begin
(

let uu____1681 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1681) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, uu____1696) -> begin
(

let uu____1701 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1701) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, uu____1716) -> begin
(

let uu____1721 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1721) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, uu____1736) -> begin
(

let uu____1741 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1741) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, uu____1756) -> begin
(

let uu____1761 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1761) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, uu____1776) -> begin
(

let uu____1781 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1781) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, uu____1796) -> begin
(

let uu____1801 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1801) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUlt, uu____1816) -> begin
(

let uu____1821 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1821) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (uu____1836), uu____1837) -> begin
(

let uu____1842 = (fresh_label1 default_msg ropt q1.FStar_SMTEncoding_Term.rng q1)
in (match (uu____1842) with
| (lab, q2) -> begin
(((lab)::labels), (q2))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Add, uu____1857) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Sub, uu____1868) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Div, uu____1879) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mul, uu____1890) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Minus, uu____1901) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mod, uu____1912) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvAnd, uu____1923) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvXor, uu____1934) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvOr, uu____1945) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvAdd, uu____1956) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvSub, uu____1967) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvShl, uu____1978) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvShr, uu____1989) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUdiv, uu____2000) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvMod, uu____2011) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvMul, uu____2022) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvUext (uu____2033), uu____2034) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.BvToNat, uu____2045) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.NatToBv (uu____2056), uu____2057) -> begin
(failwith "Impossible: non-propositional term")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, uu____2068) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, uu____2079) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body) -> begin
(

let uu____2110 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____2110) with
| (labels1, body1) -> begin
(

let uu____2129 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body1)))) q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____2129)))
end))
end
| FStar_SMTEncoding_Term.Let (es, body) -> begin
(

let uu____2146 = (aux default_msg ropt post_name_opt labels body)
in (match (uu____2146) with
| (labels1, body1) -> begin
(

let uu____2165 = (FStar_SMTEncoding_Term.mkLet ((es), (body1)) q1.FStar_SMTEncoding_Term.rng)
in ((labels1), (uu____2165)))
end))
end))
in (aux "assertion failed" FStar_Pervasives_Native.None FStar_Pervasives_Native.None [] q)))
end)))))))


let detail_errors : Prims.bool  ->  FStar_TypeChecker_Env.env  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  FStar_SMTEncoding_Z3.z3result)  ->  unit = (fun hint_replay env all_labels askZ3 -> (

let print_banner = (fun uu____2200 -> (

let msg = (

let uu____2202 = (

let uu____2203 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____2203))
in (

let uu____2204 = (FStar_Util.string_of_int (Prims.parse_int "5"))
in (

let uu____2205 = (FStar_Util.string_of_int (FStar_List.length all_labels))
in (FStar_Util.format4 "Detailed %s report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n" (match (hint_replay) with
| true -> begin
"hint replay"
end
| uu____2206 -> begin
"error"
end) uu____2202 uu____2204 uu____2205))))
in (FStar_Util.print_error msg)))
in (

let print_result = (fun uu____2222 -> (match (uu____2222) with
| ((uu____2233, msg, r), success) -> begin
(match (success) with
| true -> begin
(

let uu____2243 = (FStar_Range.string_of_range r)
in (FStar_Util.print1 "OK: proof obligation at %s was proven\n" uu____2243))
end
| uu____2244 -> begin
(match (hint_replay) with
| true -> begin
(FStar_Errors.log_issue r ((FStar_Errors.Warning_HintFailedToReplayProof), ((Prims.strcat "Hint failed to replay this sub-proof: " msg))))
end
| uu____2245 -> begin
(

let uu____2246 = (

let uu____2251 = (

let uu____2252 = (FStar_Range.string_of_range r)
in (FStar_Util.format2 "XX: proof obligation at %s failed\n\t%s\n" uu____2252 msg))
in ((FStar_Errors.Error_ProofObligationFailed), (uu____2251)))
in (FStar_Errors.log_issue r uu____2246))
end)
end)
end))
in (

let elim = (fun labs -> (FStar_All.pipe_right labs (FStar_List.map (fun uu____2314 -> (match (uu____2314) with
| (l, uu____2326, uu____2327) -> begin
(

let a = (

let uu____2337 = (

let uu____2338 = (

let uu____2343 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((uu____2343), (FStar_SMTEncoding_Util.mkTrue)))
in (FStar_SMTEncoding_Util.mkEq uu____2338))
in {FStar_SMTEncoding_Term.assumption_term = uu____2337; FStar_SMTEncoding_Term.assumption_caption = FStar_Pervasives_Native.Some ("Disabling label"); FStar_SMTEncoding_Term.assumption_name = (Prims.strcat "@disable_label_" (FStar_Pervasives_Native.fst l)); FStar_SMTEncoding_Term.assumption_fact_ids = []})
in FStar_SMTEncoding_Term.Assume (a))
end)))))
in (

let rec linear_check = (fun eliminated errors active -> ((FStar_SMTEncoding_Z3.refresh ());
(match (active) with
| [] -> begin
(

let results = (

let uu____2404 = (FStar_List.map (fun x -> ((x), (true))) eliminated)
in (

let uu____2417 = (FStar_List.map (fun x -> ((x), (false))) errors)
in (FStar_List.append uu____2404 uu____2417)))
in (sort_labels results))
end
| (hd1)::tl1 -> begin
((

let uu____2439 = (FStar_Util.string_of_int (FStar_List.length active))
in (FStar_Util.print1 "%s, " uu____2439));
(

let decls = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl1)))
in (

let result = (askZ3 decls)
in (match (result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____2470) -> begin
(linear_check ((hd1)::eliminated) errors tl1)
end
| uu____2471 -> begin
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
));
))))))





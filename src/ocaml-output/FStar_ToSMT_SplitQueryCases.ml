
let rec get_next_n_ite = (fun n t negs f -> (match ((n <= 0)) with
| true -> begin
(let _121_14 = (f FStar_ToSMT_Term.mkTrue)
in (true, _121_14, negs, t))
end
| false -> begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, g::t::e::_52_7) -> begin
(let _121_19 = (let _121_16 = (let _121_15 = (FStar_ToSMT_Term.mkNot g)
in (negs, _121_15))
in (FStar_ToSMT_Term.mkAnd _121_16))
in (get_next_n_ite (n - 1) e _121_19 (fun x -> (let _121_18 = (FStar_ToSMT_Term.mkITE (g, t, x))
in (f _121_18)))))
end
| FStar_ToSMT_Term.FreeV (_52_18) -> begin
(let _121_20 = (f FStar_ToSMT_Term.mkTrue)
in (true, _121_20, negs, t))
end
| _52_21 -> begin
(false, FStar_ToSMT_Term.mkFalse, FStar_ToSMT_Term.mkFalse, FStar_ToSMT_Term.mkFalse)
end)
end))

let rec is_ite_all_the_way = (fun n t negs l -> (match ((n <= 0)) with
| true -> begin
(Prims.raise FStar_Util.Impos)
end
| false -> begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (_52_27) -> begin
(let _121_31 = (let _121_30 = (let _121_29 = (FStar_ToSMT_Term.mkNot t)
in (negs, _121_29))
in (FStar_ToSMT_Term.mkAnd _121_30))
in (true, l, _121_31))
end
| _52_30 -> begin
(let _52_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_52_36) with
| (b, t, negs', rest) -> begin
(match (b) with
| true -> begin
(let _121_34 = (let _121_33 = (FStar_ToSMT_Term.mkImp (negs, t))
in (_121_33)::l)
in (is_ite_all_the_way n rest negs' _121_34))
end
| false -> begin
(false, [], FStar_ToSMT_Term.mkFalse)
end)
end))
end)
end))

let rec parse_query_for_split_cases = (fun n t f -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _121_61 = (FStar_ToSMT_Term.mkForall'' (l, opt, l', x))
in (f _121_61))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, t1::t2::_52_50) -> begin
(let r = (match (t2.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, _52_59, _52_61, _52_63, _52_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _121_69 = (FStar_ToSMT_Term.mkImp (t1, x))
in (f _121_69))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _52_71) -> begin
(let _52_77 = (is_ite_all_the_way n t2 FStar_ToSMT_Term.mkTrue [])
in (match (_52_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _121_78 = (FStar_ToSMT_Term.mkImp (t1, x))
in (f _121_78))), l, negs))
end))
end
| _52_80 -> begin
(false, ((fun _52_81 -> FStar_ToSMT_Term.mkFalse), [], FStar_ToSMT_Term.mkFalse))
end)
in r)
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _52_86) -> begin
(let _52_92 = (is_ite_all_the_way n t FStar_ToSMT_Term.mkTrue [])
in (match (_52_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _52_94 -> begin
(false, ((fun _52_95 -> FStar_ToSMT_Term.mkFalse), [], FStar_ToSMT_Term.mkFalse))
end))

let strip_not = (fun t -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Not, hd::_52_100) -> begin
hd
end
| _52_106 -> begin
t
end))

let rec check_split_cases = (fun f l check -> (FStar_List.iter (fun t -> (let _121_117 = (let _121_116 = (let _121_115 = (let _121_114 = (f t)
in (FStar_ToSMT_Term.mkNot _121_114))
in (_121_115, None))
in FStar_ToSMT_Term.Assume (_121_116))
in (check _121_117))) (FStar_List.rev l)))

let check_exhaustiveness = (fun f negs check -> (let _121_138 = (let _121_137 = (let _121_136 = (let _121_135 = (let _121_134 = (FStar_ToSMT_Term.mkNot negs)
in (f _121_134))
in (FStar_ToSMT_Term.mkNot _121_135))
in (_121_136, None))
in FStar_ToSMT_Term.Assume (_121_137))
in (check _121_138)))

let can_handle_query = (fun n q -> (match (q) with
| FStar_ToSMT_Term.Assume (q', _52_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _52_123 -> begin
(false, ((fun x -> x), [], FStar_ToSMT_Term.mkFalse))
end))

let handle_query = (fun _52_128 check -> (match (_52_128) with
| (f, l, negs) -> begin
(let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





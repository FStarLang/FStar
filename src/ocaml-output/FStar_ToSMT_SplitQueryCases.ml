
open Prims
let rec get_next_n_ite = (fun n t negs f -> if (n <= 0) then begin
(let _120_14 = (f FStar_ToSMT_Term.mkTrue)
in (true, _120_14, negs, t))
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, g::t::e::_53_7) -> begin
(let _120_19 = (let _120_16 = (let _120_15 = (FStar_ToSMT_Term.mkNot g)
in (negs, _120_15))
in (FStar_ToSMT_Term.mkAnd _120_16))
in (get_next_n_ite (n - 1) e _120_19 (fun x -> (let _120_18 = (FStar_ToSMT_Term.mkITE (g, t, x))
in (f _120_18)))))
end
| FStar_ToSMT_Term.FreeV (_53_18) -> begin
(let _120_20 = (f FStar_ToSMT_Term.mkTrue)
in (true, _120_20, negs, t))
end
| _53_21 -> begin
(false, FStar_ToSMT_Term.mkFalse, FStar_ToSMT_Term.mkFalse, FStar_ToSMT_Term.mkFalse)
end)
end)

let rec is_ite_all_the_way = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (_53_27) -> begin
(let _120_31 = (let _120_30 = (let _120_29 = (FStar_ToSMT_Term.mkNot t)
in (negs, _120_29))
in (FStar_ToSMT_Term.mkAnd _120_30))
in (true, l, _120_31))
end
| _53_30 -> begin
(let _53_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_53_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _120_34 = (let _120_33 = (FStar_ToSMT_Term.mkImp (negs, t))
in (_120_33)::l)
in (is_ite_all_the_way n rest negs' _120_34))
end else begin
(false, [], FStar_ToSMT_Term.mkFalse)
end
end))
end)
end)

let rec parse_query_for_split_cases = (fun n t f -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _120_61 = (FStar_ToSMT_Term.mkForall'' (l, opt, l', x))
in (f _120_61))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, t1::t2::_53_50) -> begin
(let r = (match (t2.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, _53_59, _53_61, _53_63, _53_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _120_69 = (FStar_ToSMT_Term.mkImp (t1, x))
in (f _120_69))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _53_71) -> begin
(let _53_77 = (is_ite_all_the_way n t2 FStar_ToSMT_Term.mkTrue [])
in (match (_53_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _120_78 = (FStar_ToSMT_Term.mkImp (t1, x))
in (f _120_78))), l, negs))
end))
end
| _53_80 -> begin
(false, ((fun _53_81 -> FStar_ToSMT_Term.mkFalse), [], FStar_ToSMT_Term.mkFalse))
end)
in r)
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _53_86) -> begin
(let _53_92 = (is_ite_all_the_way n t FStar_ToSMT_Term.mkTrue [])
in (match (_53_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _53_94 -> begin
(false, ((fun _53_95 -> FStar_ToSMT_Term.mkFalse), [], FStar_ToSMT_Term.mkFalse))
end))

let strip_not = (fun t -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Not, hd::_53_100) -> begin
hd
end
| _53_106 -> begin
t
end))

let rec check_split_cases = (fun f l check -> (FStar_List.iter (fun t -> (let _120_117 = (let _120_116 = (let _120_115 = (let _120_114 = (f t)
in (FStar_ToSMT_Term.mkNot _120_114))
in (_120_115, None))
in FStar_ToSMT_Term.Assume (_120_116))
in (check _120_117))) (FStar_List.rev l)))

let check_exhaustiveness = (fun f negs check -> (let _120_138 = (let _120_137 = (let _120_136 = (let _120_135 = (let _120_134 = (FStar_ToSMT_Term.mkNot negs)
in (f _120_134))
in (FStar_ToSMT_Term.mkNot _120_135))
in (_120_136, None))
in FStar_ToSMT_Term.Assume (_120_137))
in (check _120_138)))

let can_handle_query = (fun n q -> (match (q) with
| FStar_ToSMT_Term.Assume (q', _53_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _53_123 -> begin
(false, ((fun x -> x), [], FStar_ToSMT_Term.mkFalse))
end))

let handle_query = (fun _53_128 check -> (match (_53_128) with
| (f, l, negs) -> begin
(let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





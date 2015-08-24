
let rec get_next_n_ite = (fun ( n ) ( t ) ( negs ) ( f ) -> (match ((n <= 0)) with
| true -> begin
(let _117_14 = (f Microsoft_FStar_ToSMT_Term.mkTrue)
in (true, _117_14, negs, t))
end
| false -> begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, g::t::e::_51_7)) -> begin
(let _117_19 = (let _117_16 = (let _117_15 = (Microsoft_FStar_ToSMT_Term.mkNot g)
in (negs, _117_15))
in (Microsoft_FStar_ToSMT_Term.mkAnd _117_16))
in (get_next_n_ite (n - 1) e _117_19 (fun ( x ) -> (let _117_18 = (Microsoft_FStar_ToSMT_Term.mkITE (g, t, x))
in (f _117_18)))))
end
| Microsoft_FStar_ToSMT_Term.FreeV (_51_18) -> begin
(let _117_20 = (f Microsoft_FStar_ToSMT_Term.mkTrue)
in (true, _117_20, negs, t))
end
| _51_21 -> begin
(false, Microsoft_FStar_ToSMT_Term.mkFalse, Microsoft_FStar_ToSMT_Term.mkFalse, Microsoft_FStar_ToSMT_Term.mkFalse)
end)
end))

let rec is_ite_all_the_way = (fun ( n ) ( t ) ( negs ) ( l ) -> (match ((n <= 0)) with
| true -> begin
(raise (Support.Microsoft.FStar.Util.Impos))
end
| false -> begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.FreeV (_51_27) -> begin
(let _117_31 = (let _117_30 = (let _117_29 = (Microsoft_FStar_ToSMT_Term.mkNot t)
in (negs, _117_29))
in (Microsoft_FStar_ToSMT_Term.mkAnd _117_30))
in (true, l, _117_31))
end
| _51_30 -> begin
(let _51_36 = (get_next_n_ite n t negs (fun ( x ) -> x))
in (match (_51_36) with
| (b, t, negs', rest) -> begin
(match (b) with
| true -> begin
(let _117_34 = (let _117_33 = (Microsoft_FStar_ToSMT_Term.mkImp (negs, t))
in (_117_33)::l)
in (is_ite_all_the_way n rest negs' _117_34))
end
| false -> begin
(false, [], Microsoft_FStar_ToSMT_Term.mkFalse)
end)
end))
end)
end))

let rec parse_query_for_split_cases = (fun ( n ) ( t ) ( f ) -> (match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.Quant ((Microsoft_FStar_ToSMT_Term.Forall, l, opt, l', t)) -> begin
(parse_query_for_split_cases n t (fun ( x ) -> (let _117_61 = (Microsoft_FStar_ToSMT_Term.mkForall'' (l, opt, l', x))
in (f _117_61))))
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Imp, t1::t2::_51_50)) -> begin
(let r = (match (t2.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.Quant ((Microsoft_FStar_ToSMT_Term.Forall, _51_59, _51_61, _51_63, _51_65)) -> begin
(parse_query_for_split_cases n t2 (fun ( x ) -> (let _117_69 = (Microsoft_FStar_ToSMT_Term.mkImp (t1, x))
in (f _117_69))))
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, _51_71)) -> begin
(let _51_77 = (is_ite_all_the_way n t2 Microsoft_FStar_ToSMT_Term.mkTrue [])
in (match (_51_77) with
| (b, l, negs) -> begin
(b, ((fun ( x ) -> (let _117_78 = (Microsoft_FStar_ToSMT_Term.mkImp (t1, x))
in (f _117_78))), l, negs))
end))
end
| _51_80 -> begin
(false, ((fun ( _51_81 ) -> Microsoft_FStar_ToSMT_Term.mkFalse), [], Microsoft_FStar_ToSMT_Term.mkFalse))
end)
in r)
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, _51_86)) -> begin
(let _51_92 = (is_ite_all_the_way n t Microsoft_FStar_ToSMT_Term.mkTrue [])
in (match (_51_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _51_94 -> begin
(false, ((fun ( _51_95 ) -> Microsoft_FStar_ToSMT_Term.mkFalse), [], Microsoft_FStar_ToSMT_Term.mkFalse))
end))

let strip_not = (fun ( t ) -> (match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Not, hd::_51_100)) -> begin
hd
end
| _51_106 -> begin
t
end))

let rec check_split_cases = (fun ( f ) ( l ) ( check ) -> (Support.List.iter (fun ( t ) -> (let _117_117 = (let _117_116 = (let _117_115 = (let _117_114 = (f t)
in (Microsoft_FStar_ToSMT_Term.mkNot _117_114))
in (_117_115, None))
in Microsoft_FStar_ToSMT_Term.Assume (_117_116))
in (check _117_117))) (Support.List.rev l)))

let check_exhaustiveness = (fun ( f ) ( negs ) ( check ) -> (let _117_138 = (let _117_137 = (let _117_136 = (let _117_135 = (let _117_134 = (Microsoft_FStar_ToSMT_Term.mkNot negs)
in (f _117_134))
in (Microsoft_FStar_ToSMT_Term.mkNot _117_135))
in (_117_136, None))
in Microsoft_FStar_ToSMT_Term.Assume (_117_137))
in (check _117_138)))

let can_handle_query = (fun ( n ) ( q ) -> (match (q) with
| Microsoft_FStar_ToSMT_Term.Assume ((q', _51_118)) -> begin
(parse_query_for_split_cases n (strip_not q') (fun ( x ) -> x))
end
| _51_123 -> begin
(false, ((fun ( x ) -> x), [], Microsoft_FStar_ToSMT_Term.mkFalse))
end))

let handle_query = (fun ( _51_128 ) ( check ) -> (match (_51_128) with
| (f, l, negs) -> begin
(let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





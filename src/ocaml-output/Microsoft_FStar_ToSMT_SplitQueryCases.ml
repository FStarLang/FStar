
let rec get_next_n_ite = (fun ( n ) ( t ) ( negs ) ( f ) -> (match ((n <= 0)) with
| true -> begin
(let _68_21103 = (f Microsoft_FStar_ToSMT_Term.mkTrue)
in (true, _68_21103, negs, t))
end
| false -> begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, g::t::e::_49_7)) -> begin
(let _68_21108 = (let _68_21105 = (let _68_21104 = (Microsoft_FStar_ToSMT_Term.mkNot g)
in (negs, _68_21104))
in (Microsoft_FStar_ToSMT_Term.mkAnd _68_21105))
in (get_next_n_ite (n - 1) e _68_21108 (fun ( x ) -> (let _68_21107 = (Microsoft_FStar_ToSMT_Term.mkITE (g, t, x))
in (f _68_21107)))))
end
| Microsoft_FStar_ToSMT_Term.FreeV (_49_18) -> begin
(let _68_21109 = (f Microsoft_FStar_ToSMT_Term.mkTrue)
in (true, _68_21109, negs, t))
end
| _49_21 -> begin
(false, Microsoft_FStar_ToSMT_Term.mkFalse, Microsoft_FStar_ToSMT_Term.mkFalse, Microsoft_FStar_ToSMT_Term.mkFalse)
end)
end))

let rec is_ite_all_the_way = (fun ( n ) ( t ) ( negs ) ( l ) -> (match ((n <= 0)) with
| true -> begin
(raise (Support.Microsoft.FStar.Util.Impos))
end
| false -> begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.FreeV (_49_27) -> begin
(let _68_21120 = (let _68_21119 = (let _68_21118 = (Microsoft_FStar_ToSMT_Term.mkNot t)
in (negs, _68_21118))
in (Microsoft_FStar_ToSMT_Term.mkAnd _68_21119))
in (true, l, _68_21120))
end
| _49_30 -> begin
(let _49_36 = (get_next_n_ite n t negs (fun ( x ) -> x))
in (match (_49_36) with
| (b, t, negs', rest) -> begin
(match (b) with
| true -> begin
(let _68_21123 = (let _68_21122 = (Microsoft_FStar_ToSMT_Term.mkImp (negs, t))
in (_68_21122)::l)
in (is_ite_all_the_way n rest negs' _68_21123))
end
| false -> begin
(false, [], Microsoft_FStar_ToSMT_Term.mkFalse)
end)
end))
end)
end))

let rec parse_query_for_split_cases = (fun ( n ) ( t ) ( f ) -> (match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.Quant ((Microsoft_FStar_ToSMT_Term.Forall, l, opt, l', t)) -> begin
(parse_query_for_split_cases n t (fun ( x ) -> (let _68_21150 = (Microsoft_FStar_ToSMT_Term.mkForall'' (l, opt, l', x))
in (f _68_21150))))
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Imp, t1::t2::_49_50)) -> begin
(let r = (match (t2.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.Quant ((Microsoft_FStar_ToSMT_Term.Forall, _49_59, _49_61, _49_63, _49_65)) -> begin
(parse_query_for_split_cases n t2 (fun ( x ) -> (let _68_21158 = (Microsoft_FStar_ToSMT_Term.mkImp (t1, x))
in (f _68_21158))))
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, _49_71)) -> begin
(let _49_77 = (is_ite_all_the_way n t2 Microsoft_FStar_ToSMT_Term.mkTrue [])
in (match (_49_77) with
| (b, l, negs) -> begin
(b, ((fun ( x ) -> (let _68_21167 = (Microsoft_FStar_ToSMT_Term.mkImp (t1, x))
in (f _68_21167))), l, negs))
end))
end
| _49_80 -> begin
(false, ((fun ( _49_81 ) -> Microsoft_FStar_ToSMT_Term.mkFalse), [], Microsoft_FStar_ToSMT_Term.mkFalse))
end)
in r)
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, _49_86)) -> begin
(let _49_92 = (is_ite_all_the_way n t Microsoft_FStar_ToSMT_Term.mkTrue [])
in (match (_49_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _49_94 -> begin
(false, ((fun ( _49_95 ) -> Microsoft_FStar_ToSMT_Term.mkFalse), [], Microsoft_FStar_ToSMT_Term.mkFalse))
end))

let strip_not = (fun ( t ) -> (match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Not, hd::_49_100)) -> begin
hd
end
| _49_106 -> begin
t
end))

let rec check_split_cases = (fun ( f ) ( l ) ( check ) -> (Support.List.iter (fun ( t ) -> (let _68_21206 = (let _68_21205 = (let _68_21204 = (let _68_21203 = (f t)
in (Microsoft_FStar_ToSMT_Term.mkNot _68_21203))
in (_68_21204, None))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21205))
in (check _68_21206))) (Support.List.rev l)))

let check_exhaustiveness = (fun ( f ) ( negs ) ( check ) -> (let _68_21227 = (let _68_21226 = (let _68_21225 = (let _68_21224 = (let _68_21223 = (Microsoft_FStar_ToSMT_Term.mkNot negs)
in (f _68_21223))
in (Microsoft_FStar_ToSMT_Term.mkNot _68_21224))
in (_68_21225, None))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21226))
in (check _68_21227)))

let can_handle_query = (fun ( n ) ( q ) -> (match (q) with
| Microsoft_FStar_ToSMT_Term.Assume ((q', _49_118)) -> begin
(parse_query_for_split_cases n (strip_not q') (fun ( x ) -> x))
end
| _49_123 -> begin
(false, ((fun ( x ) -> x), [], Microsoft_FStar_ToSMT_Term.mkFalse))
end))

let handle_query = (fun ( _49_128 ) ( check ) -> (match (_49_128) with
| (f, l, negs) -> begin
(let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





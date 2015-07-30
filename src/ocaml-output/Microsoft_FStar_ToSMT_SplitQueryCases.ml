
let rec get_next_n_ite = (fun ( n ) ( t ) ( negs ) ( f ) -> (match ((n <= 0)) with
| true -> begin
(let _65_21060 = (f Microsoft_FStar_ToSMT_Term.mkTrue)
in (true, _65_21060, negs, t))
end
| false -> begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, g::t::e::_)) -> begin
(let _65_21065 = (let _65_21062 = (let _65_21061 = (Microsoft_FStar_ToSMT_Term.mkNot g)
in (negs, _65_21061))
in (Microsoft_FStar_ToSMT_Term.mkAnd _65_21062))
in (get_next_n_ite (n - 1) e _65_21065 (fun ( x ) -> (let _65_21064 = (Microsoft_FStar_ToSMT_Term.mkITE (g, t, x))
in (f _65_21064)))))
end
| Microsoft_FStar_ToSMT_Term.FreeV (_) -> begin
(let _65_21066 = (f Microsoft_FStar_ToSMT_Term.mkTrue)
in (true, _65_21066, negs, t))
end
| _ -> begin
(false, Microsoft_FStar_ToSMT_Term.mkFalse, Microsoft_FStar_ToSMT_Term.mkFalse, Microsoft_FStar_ToSMT_Term.mkFalse)
end)
end))

let rec is_ite_all_the_way = (fun ( n ) ( t ) ( negs ) ( l ) -> (match ((n <= 0)) with
| true -> begin
(raise (Support.Microsoft.FStar.Util.Impos))
end
| false -> begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.FreeV (_) -> begin
(let _65_21077 = (let _65_21076 = (let _65_21075 = (Microsoft_FStar_ToSMT_Term.mkNot t)
in (negs, _65_21075))
in (Microsoft_FStar_ToSMT_Term.mkAnd _65_21076))
in (true, l, _65_21077))
end
| _ -> begin
(let _49_36 = (get_next_n_ite n t negs (fun ( x ) -> x))
in (match (_49_36) with
| (b, t, negs', rest) -> begin
(match (b) with
| true -> begin
(let _65_21080 = (let _65_21079 = (Microsoft_FStar_ToSMT_Term.mkImp (negs, t))
in (_65_21079)::l)
in (is_ite_all_the_way n rest negs' _65_21080))
end
| false -> begin
(false, [], Microsoft_FStar_ToSMT_Term.mkFalse)
end)
end))
end)
end))

let rec parse_query_for_split_cases = (fun ( n ) ( t ) ( f ) -> (match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.Quant ((Microsoft_FStar_ToSMT_Term.Forall, l, opt, l', t)) -> begin
(parse_query_for_split_cases n t (fun ( x ) -> (let _65_21107 = (Microsoft_FStar_ToSMT_Term.mkForall'' (l, opt, l', x))
in (f _65_21107))))
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Imp, t1::t2::_)) -> begin
(let r = (match (t2.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.Quant ((Microsoft_FStar_ToSMT_Term.Forall, _, _, _, _)) -> begin
(parse_query_for_split_cases n t2 (fun ( x ) -> (let _65_21115 = (Microsoft_FStar_ToSMT_Term.mkImp (t1, x))
in (f _65_21115))))
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, _)) -> begin
(let _49_77 = (is_ite_all_the_way n t2 Microsoft_FStar_ToSMT_Term.mkTrue [])
in (match (_49_77) with
| (b, l, negs) -> begin
(b, ((fun ( x ) -> (let _65_21124 = (Microsoft_FStar_ToSMT_Term.mkImp (t1, x))
in (f _65_21124))), l, negs))
end))
end
| _ -> begin
(false, ((fun ( _49_81 ) -> Microsoft_FStar_ToSMT_Term.mkFalse), [], Microsoft_FStar_ToSMT_Term.mkFalse))
end)
in r)
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, _)) -> begin
(let _49_92 = (is_ite_all_the_way n t Microsoft_FStar_ToSMT_Term.mkTrue [])
in (match (_49_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _ -> begin
(false, ((fun ( _49_95 ) -> Microsoft_FStar_ToSMT_Term.mkFalse), [], Microsoft_FStar_ToSMT_Term.mkFalse))
end))

let strip_not = (fun ( t ) -> (match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Not, hd::_)) -> begin
hd
end
| _ -> begin
t
end))

let rec check_split_cases = (fun ( f ) ( l ) ( check ) -> (Support.List.iter (fun ( t ) -> (let _65_21163 = (let _65_21162 = (let _65_21161 = (let _65_21160 = (f t)
in (Microsoft_FStar_ToSMT_Term.mkNot _65_21160))
in (_65_21161, None))
in Microsoft_FStar_ToSMT_Term.Assume (_65_21162))
in (check _65_21163))) (Support.List.rev l)))

let check_exhaustiveness = (fun ( f ) ( negs ) ( check ) -> (let _65_21184 = (let _65_21183 = (let _65_21182 = (let _65_21181 = (let _65_21180 = (Microsoft_FStar_ToSMT_Term.mkNot negs)
in (f _65_21180))
in (Microsoft_FStar_ToSMT_Term.mkNot _65_21181))
in (_65_21182, None))
in Microsoft_FStar_ToSMT_Term.Assume (_65_21183))
in (check _65_21184)))

let can_handle_query = (fun ( n ) ( q ) -> (match (q) with
| Microsoft_FStar_ToSMT_Term.Assume ((q', _)) -> begin
(parse_query_for_split_cases n (strip_not q') (fun ( x ) -> x))
end
| _ -> begin
(false, ((fun ( x ) -> x), [], Microsoft_FStar_ToSMT_Term.mkFalse))
end))

let handle_query = (fun ( _49_128 ) ( check ) -> (match (_49_128) with
| (f, l, negs) -> begin
(let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





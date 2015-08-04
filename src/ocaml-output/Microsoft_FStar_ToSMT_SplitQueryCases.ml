
let rec get_next_n_ite = (fun ( n ) ( t ) ( negs ) ( f ) -> (match ((n <= 0)) with
| true -> begin
(let _68_21075 = (f Microsoft_FStar_ToSMT_Term.mkTrue)
in (true, _68_21075, negs, t))
end
| false -> begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, g::t::e::_)) -> begin
(let _68_21080 = (let _68_21077 = (let _68_21076 = (Microsoft_FStar_ToSMT_Term.mkNot g)
in (negs, _68_21076))
in (Microsoft_FStar_ToSMT_Term.mkAnd _68_21077))
in (get_next_n_ite (n - 1) e _68_21080 (fun ( x ) -> (let _68_21079 = (Microsoft_FStar_ToSMT_Term.mkITE (g, t, x))
in (f _68_21079)))))
end
| Microsoft_FStar_ToSMT_Term.FreeV (_) -> begin
(let _68_21081 = (f Microsoft_FStar_ToSMT_Term.mkTrue)
in (true, _68_21081, negs, t))
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
(let _68_21092 = (let _68_21091 = (let _68_21090 = (Microsoft_FStar_ToSMT_Term.mkNot t)
in (negs, _68_21090))
in (Microsoft_FStar_ToSMT_Term.mkAnd _68_21091))
in (true, l, _68_21092))
end
| _ -> begin
(let _49_36 = (get_next_n_ite n t negs (fun ( x ) -> x))
in (match (_49_36) with
| (b, t, negs', rest) -> begin
(match (b) with
| true -> begin
(let _68_21095 = (let _68_21094 = (Microsoft_FStar_ToSMT_Term.mkImp (negs, t))
in (_68_21094)::l)
in (is_ite_all_the_way n rest negs' _68_21095))
end
| false -> begin
(false, [], Microsoft_FStar_ToSMT_Term.mkFalse)
end)
end))
end)
end))

let rec parse_query_for_split_cases = (fun ( n ) ( t ) ( f ) -> (match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.Quant ((Microsoft_FStar_ToSMT_Term.Forall, l, opt, l', t)) -> begin
(parse_query_for_split_cases n t (fun ( x ) -> (let _68_21122 = (Microsoft_FStar_ToSMT_Term.mkForall'' (l, opt, l', x))
in (f _68_21122))))
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Imp, t1::t2::_)) -> begin
(let r = (match (t2.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.Quant ((Microsoft_FStar_ToSMT_Term.Forall, _, _, _, _)) -> begin
(parse_query_for_split_cases n t2 (fun ( x ) -> (let _68_21130 = (Microsoft_FStar_ToSMT_Term.mkImp (t1, x))
in (f _68_21130))))
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, _)) -> begin
(let _49_77 = (is_ite_all_the_way n t2 Microsoft_FStar_ToSMT_Term.mkTrue [])
in (match (_49_77) with
| (b, l, negs) -> begin
(b, ((fun ( x ) -> (let _68_21139 = (Microsoft_FStar_ToSMT_Term.mkImp (t1, x))
in (f _68_21139))), l, negs))
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

let rec check_split_cases = (fun ( f ) ( l ) ( check ) -> (Support.List.iter (fun ( t ) -> (let _68_21178 = (let _68_21177 = (let _68_21176 = (let _68_21175 = (f t)
in (Microsoft_FStar_ToSMT_Term.mkNot _68_21175))
in (_68_21176, None))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21177))
in (check _68_21178))) (Support.List.rev l)))

let check_exhaustiveness = (fun ( f ) ( negs ) ( check ) -> (let _68_21199 = (let _68_21198 = (let _68_21197 = (let _68_21196 = (let _68_21195 = (Microsoft_FStar_ToSMT_Term.mkNot negs)
in (f _68_21195))
in (Microsoft_FStar_ToSMT_Term.mkNot _68_21196))
in (_68_21197, None))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21198))
in (check _68_21199)))

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





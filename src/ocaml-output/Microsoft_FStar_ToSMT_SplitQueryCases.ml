
let rec get_next_n_ite = (fun ( n ) ( t ) ( negs ) ( f ) -> (match ((n <= 0)) with
| true -> begin
(let _68_21072 = (f Microsoft_FStar_ToSMT_Term.mkTrue)
in (true, _68_21072, negs, t))
end
| false -> begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, g::t::e::_)) -> begin
(let _68_21077 = (let _68_21074 = (let _68_21073 = (Microsoft_FStar_ToSMT_Term.mkNot g)
in (negs, _68_21073))
in (Microsoft_FStar_ToSMT_Term.mkAnd _68_21074))
in (get_next_n_ite (n - 1) e _68_21077 (fun ( x ) -> (let _68_21076 = (Microsoft_FStar_ToSMT_Term.mkITE (g, t, x))
in (f _68_21076)))))
end
| Microsoft_FStar_ToSMT_Term.FreeV (_) -> begin
(let _68_21078 = (f Microsoft_FStar_ToSMT_Term.mkTrue)
in (true, _68_21078, negs, t))
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
(let _68_21089 = (let _68_21088 = (let _68_21087 = (Microsoft_FStar_ToSMT_Term.mkNot t)
in (negs, _68_21087))
in (Microsoft_FStar_ToSMT_Term.mkAnd _68_21088))
in (true, l, _68_21089))
end
| _ -> begin
(let _49_36 = (get_next_n_ite n t negs (fun ( x ) -> x))
in (match (_49_36) with
| (b, t, negs', rest) -> begin
(match (b) with
| true -> begin
(let _68_21092 = (let _68_21091 = (Microsoft_FStar_ToSMT_Term.mkImp (negs, t))
in (_68_21091)::l)
in (is_ite_all_the_way n rest negs' _68_21092))
end
| false -> begin
(false, [], Microsoft_FStar_ToSMT_Term.mkFalse)
end)
end))
end)
end))

let rec parse_query_for_split_cases = (fun ( n ) ( t ) ( f ) -> (match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.Quant ((Microsoft_FStar_ToSMT_Term.Forall, l, opt, l', t)) -> begin
(parse_query_for_split_cases n t (fun ( x ) -> (let _68_21119 = (Microsoft_FStar_ToSMT_Term.mkForall'' (l, opt, l', x))
in (f _68_21119))))
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Imp, t1::t2::_)) -> begin
(let r = (match (t2.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.Quant ((Microsoft_FStar_ToSMT_Term.Forall, _, _, _, _)) -> begin
(parse_query_for_split_cases n t2 (fun ( x ) -> (let _68_21127 = (Microsoft_FStar_ToSMT_Term.mkImp (t1, x))
in (f _68_21127))))
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, _)) -> begin
(let _49_77 = (is_ite_all_the_way n t2 Microsoft_FStar_ToSMT_Term.mkTrue [])
in (match (_49_77) with
| (b, l, negs) -> begin
(b, ((fun ( x ) -> (let _68_21136 = (Microsoft_FStar_ToSMT_Term.mkImp (t1, x))
in (f _68_21136))), l, negs))
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

let rec check_split_cases = (fun ( f ) ( l ) ( check ) -> (Support.List.iter (fun ( t ) -> (let _68_21175 = (let _68_21174 = (let _68_21173 = (let _68_21172 = (f t)
in (Microsoft_FStar_ToSMT_Term.mkNot _68_21172))
in (_68_21173, None))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21174))
in (check _68_21175))) (Support.List.rev l)))

let check_exhaustiveness = (fun ( f ) ( negs ) ( check ) -> (let _68_21196 = (let _68_21195 = (let _68_21194 = (let _68_21193 = (let _68_21192 = (Microsoft_FStar_ToSMT_Term.mkNot negs)
in (f _68_21192))
in (Microsoft_FStar_ToSMT_Term.mkNot _68_21193))
in (_68_21194, None))
in Microsoft_FStar_ToSMT_Term.Assume (_68_21195))
in (check _68_21196)))

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





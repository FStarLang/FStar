
let rec get_next_n_ite = (fun ( n  :  int ) ( t  :  Microsoft_FStar_ToSMT_Term.term ) ( negs  :  Microsoft_FStar_ToSMT_Term.term ) ( f  :  Microsoft_FStar_ToSMT_Term.term  ->  Microsoft_FStar_ToSMT_Term.term ) -> (match ((n <= 0)) with
| true -> begin
(let _52_17807 = (f Microsoft_FStar_ToSMT_Term.mkTrue)
in (true, _52_17807, negs, t))
end
| false -> begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, g::t::e::_)) -> begin
(let _52_17812 = (let _52_17809 = (let _52_17808 = (Microsoft_FStar_ToSMT_Term.mkNot g)
in (negs, _52_17808))
in (Microsoft_FStar_ToSMT_Term.mkAnd _52_17809))
in (get_next_n_ite (n - 1) e _52_17812 (fun ( x  :  Microsoft_FStar_ToSMT_Term.term ) -> (let _52_17811 = (Microsoft_FStar_ToSMT_Term.mkITE (g, t, x))
in (f _52_17811)))))
end
| Microsoft_FStar_ToSMT_Term.FreeV (_) -> begin
(let _52_17813 = (f Microsoft_FStar_ToSMT_Term.mkTrue)
in (true, _52_17813, negs, t))
end
| _ -> begin
(false, Microsoft_FStar_ToSMT_Term.mkFalse, Microsoft_FStar_ToSMT_Term.mkFalse, Microsoft_FStar_ToSMT_Term.mkFalse)
end)
end))

let rec is_ite_all_the_way = (fun ( n  :  int ) ( t  :  Microsoft_FStar_ToSMT_Term.term ) ( negs  :  Microsoft_FStar_ToSMT_Term.term ) ( l  :  Microsoft_FStar_ToSMT_Term.term list ) -> (match ((n <= 0)) with
| true -> begin
(raise (Support.Microsoft.FStar.Util.Impos))
end
| false -> begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.FreeV (_) -> begin
(let _52_17824 = (let _52_17823 = (let _52_17822 = (Microsoft_FStar_ToSMT_Term.mkNot t)
in (negs, _52_17822))
in (Microsoft_FStar_ToSMT_Term.mkAnd _52_17823))
in (true, l, _52_17824))
end
| _ -> begin
(let _49_36 = (get_next_n_ite n t negs (fun ( x  :  Microsoft_FStar_ToSMT_Term.term ) -> x))
in (match (_49_36) with
| (b, t, negs', rest) -> begin
(match (b) with
| true -> begin
(let _52_17827 = (let _52_17826 = (Microsoft_FStar_ToSMT_Term.mkImp (negs, t))
in (_52_17826)::l)
in (is_ite_all_the_way n rest negs' _52_17827))
end
| false -> begin
(false, [], Microsoft_FStar_ToSMT_Term.mkFalse)
end)
end))
end)
end))

let rec parse_query_for_split_cases = (fun ( n  :  int ) ( t  :  Microsoft_FStar_ToSMT_Term.term ) ( f  :  Microsoft_FStar_ToSMT_Term.term  ->  Microsoft_FStar_ToSMT_Term.term ) -> (match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.Quant ((Microsoft_FStar_ToSMT_Term.Forall, l, opt, l', t)) -> begin
(parse_query_for_split_cases n t (fun ( x  :  Microsoft_FStar_ToSMT_Term.term ) -> (let _52_17854 = (Microsoft_FStar_ToSMT_Term.mkForall'' (l, opt, l', x))
in (f _52_17854))))
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Imp, t1::t2::_)) -> begin
(let r = (match (t2.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.Quant ((Microsoft_FStar_ToSMT_Term.Forall, _, _, _, _)) -> begin
(parse_query_for_split_cases n t2 (fun ( x  :  Microsoft_FStar_ToSMT_Term.term ) -> (let _52_17862 = (Microsoft_FStar_ToSMT_Term.mkImp (t1, x))
in (f _52_17862))))
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, _)) -> begin
(let _49_77 = (is_ite_all_the_way n t2 Microsoft_FStar_ToSMT_Term.mkTrue [])
in (match (_49_77) with
| (b, l, negs) -> begin
(b, ((fun ( x  :  Microsoft_FStar_ToSMT_Term.term ) -> (let _52_17871 = (Microsoft_FStar_ToSMT_Term.mkImp (t1, x))
in (f _52_17871))), l, negs))
end))
end
| _ -> begin
(false, ((fun ( _49_81  :  Microsoft_FStar_ToSMT_Term.term ) -> Microsoft_FStar_ToSMT_Term.mkFalse), [], Microsoft_FStar_ToSMT_Term.mkFalse))
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
(false, ((fun ( _49_95  :  Microsoft_FStar_ToSMT_Term.term ) -> Microsoft_FStar_ToSMT_Term.mkFalse), [], Microsoft_FStar_ToSMT_Term.mkFalse))
end))

let strip_not = (fun ( t  :  Microsoft_FStar_ToSMT_Term.term ) -> (match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Not, hd::_)) -> begin
hd
end
| _ -> begin
t
end))

let rec check_split_cases = (fun ( f  :  Microsoft_FStar_ToSMT_Term.term  ->  Microsoft_FStar_ToSMT_Term.term ) ( l  :  Microsoft_FStar_ToSMT_Term.term list ) ( check  :  Microsoft_FStar_ToSMT_Term.decl  ->  unit ) -> (Support.List.iter (fun ( t  :  Microsoft_FStar_ToSMT_Term.term ) -> (let _52_17910 = (let _52_17909 = (let _52_17908 = (let _52_17907 = (f t)
in (Microsoft_FStar_ToSMT_Term.mkNot _52_17907))
in (_52_17908, None))
in Microsoft_FStar_ToSMT_Term.Assume (_52_17909))
in (check _52_17910))) (Support.List.rev l)))

let check_exhaustiveness = (fun ( f  :  Microsoft_FStar_ToSMT_Term.term  ->  Microsoft_FStar_ToSMT_Term.term ) ( negs  :  Microsoft_FStar_ToSMT_Term.term ) ( check  :  Microsoft_FStar_ToSMT_Term.decl  ->  unit ) -> (let _52_17931 = (let _52_17930 = (let _52_17929 = (let _52_17928 = (let _52_17927 = (Microsoft_FStar_ToSMT_Term.mkNot negs)
in (f _52_17927))
in (Microsoft_FStar_ToSMT_Term.mkNot _52_17928))
in (_52_17929, None))
in Microsoft_FStar_ToSMT_Term.Assume (_52_17930))
in (check _52_17931)))

let can_handle_query = (fun ( n  :  int ) ( q  :  Microsoft_FStar_ToSMT_Term.decl ) -> (match (q) with
| Microsoft_FStar_ToSMT_Term.Assume ((q', _)) -> begin
(parse_query_for_split_cases n (strip_not q') (fun ( x  :  Microsoft_FStar_ToSMT_Term.term ) -> x))
end
| _ -> begin
(false, ((fun ( x  :  Microsoft_FStar_ToSMT_Term.term ) -> x), [], Microsoft_FStar_ToSMT_Term.mkFalse))
end))

let handle_query = (fun ( _49_128  :  ((Microsoft_FStar_ToSMT_Term.term  ->  Microsoft_FStar_ToSMT_Term.term) * Microsoft_FStar_ToSMT_Term.term list * Microsoft_FStar_ToSMT_Term.term) ) ( check  :  Microsoft_FStar_ToSMT_Term.decl  ->  unit ) -> (match (_49_128) with
| (f, l, negs) -> begin
(let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





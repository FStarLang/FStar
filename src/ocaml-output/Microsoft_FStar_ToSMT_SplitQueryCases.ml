
let rec get_next_n_ite = (fun n t negs f -> if (n <= 0) then begin
(true, (f Microsoft_FStar_ToSMT_Term.mkTrue), negs, t)
end else begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, g::t::e::_)) -> begin
(get_next_n_ite (n - 1) e (Microsoft_FStar_ToSMT_Term.mkAnd (negs, (Microsoft_FStar_ToSMT_Term.mkNot g))) (fun x -> (f (Microsoft_FStar_ToSMT_Term.mkITE (g, t, x)))))
end
| Microsoft_FStar_ToSMT_Term.FreeV (_) -> begin
(true, (f Microsoft_FStar_ToSMT_Term.mkTrue), negs, t)
end
| _ -> begin
(false, Microsoft_FStar_ToSMT_Term.mkFalse, Microsoft_FStar_ToSMT_Term.mkFalse, Microsoft_FStar_ToSMT_Term.mkFalse)
end)
end)

let rec is_ite_all_the_way = (fun n t negs l -> if (n <= 0) then begin
(raise (Support.Microsoft.FStar.Util.Impos))
end else begin
(match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.FreeV (_) -> begin
(true, l, (Microsoft_FStar_ToSMT_Term.mkAnd (negs, (Microsoft_FStar_ToSMT_Term.mkNot t))))
end
| _ -> begin
(let _44_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_44_36) with
| (b, t, negs', rest) -> begin
if b then begin
(is_ite_all_the_way n rest negs' (((Microsoft_FStar_ToSMT_Term.mkImp (negs, t)))::l))
end else begin
(false, [], Microsoft_FStar_ToSMT_Term.mkFalse)
end
end))
end)
end)

let rec parse_query_for_split_cases = (fun n t f -> (match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.Quant ((Microsoft_FStar_ToSMT_Term.Forall, l, opt, l', t)) -> begin
(parse_query_for_split_cases n t (fun x -> (f (Microsoft_FStar_ToSMT_Term.mkForall'' (l, opt, l', x)))))
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Imp, t1::t2::_)) -> begin
(let r = (match (t2.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.Quant ((Microsoft_FStar_ToSMT_Term.Forall, _, _, _, _)) -> begin
(parse_query_for_split_cases n t2 (fun x -> (f (Microsoft_FStar_ToSMT_Term.mkImp (t1, x)))))
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, _)) -> begin
(let _44_77 = (is_ite_all_the_way n t2 Microsoft_FStar_ToSMT_Term.mkTrue [])
in (match (_44_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (f (Microsoft_FStar_ToSMT_Term.mkImp (t1, x)))), l, negs))
end))
end
| _ -> begin
(false, ((fun _44_81 -> Microsoft_FStar_ToSMT_Term.mkFalse), [], Microsoft_FStar_ToSMT_Term.mkFalse))
end)
in r)
end
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.ITE, _)) -> begin
(let _44_92 = (is_ite_all_the_way n t Microsoft_FStar_ToSMT_Term.mkTrue [])
in (match (_44_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _ -> begin
(false, ((fun _44_95 -> Microsoft_FStar_ToSMT_Term.mkFalse), [], Microsoft_FStar_ToSMT_Term.mkFalse))
end))

let strip_not = (fun t -> (match (t.Microsoft_FStar_ToSMT_Term.tm) with
| Microsoft_FStar_ToSMT_Term.App ((Microsoft_FStar_ToSMT_Term.Not, hd::_)) -> begin
hd
end
| _ -> begin
t
end))

let rec check_split_cases = (fun f l check -> (Support.List.iter (fun t -> (check (Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkNot (f t)), None))))) (Support.List.rev l)))

let check_exhaustiveness = (fun f negs check -> (check (Microsoft_FStar_ToSMT_Term.Assume (((Microsoft_FStar_ToSMT_Term.mkNot (f (Microsoft_FStar_ToSMT_Term.mkNot negs))), None)))))

let can_handle_query = (fun n q -> (match (q) with
| Microsoft_FStar_ToSMT_Term.Assume ((q', _)) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _ -> begin
(false, ((fun x -> x), [], Microsoft_FStar_ToSMT_Term.mkFalse))
end))

let handle_query = (fun _44_128 check -> (match (_44_128) with
| (f, l, negs) -> begin
(let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





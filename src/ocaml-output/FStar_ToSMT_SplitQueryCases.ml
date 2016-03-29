
open Prims
# 10 "FStar.ToSMT.SplitQueryCases.fst"
let rec get_next_n_ite : Prims.int  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  (Prims.bool * FStar_ToSMT_Term.term * FStar_ToSMT_Term.term * FStar_ToSMT_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _118_14 = (f FStar_ToSMT_Term.mkTrue)
in (true, _118_14, negs, t))
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, g::t::e::_39_7) -> begin
(let _118_19 = (let _118_16 = (let _118_15 = (FStar_ToSMT_Term.mkNot g)
in (negs, _118_15))
in (FStar_ToSMT_Term.mkAnd _118_16))
in (get_next_n_ite (n - 1) e _118_19 (fun x -> (let _118_18 = (FStar_ToSMT_Term.mkITE (g, t, x))
in (f _118_18)))))
end
| FStar_ToSMT_Term.FreeV (_39_18) -> begin
(let _118_20 = (f FStar_ToSMT_Term.mkTrue)
in (true, _118_20, negs, t))
end
| _39_21 -> begin
(false, FStar_ToSMT_Term.mkFalse, FStar_ToSMT_Term.mkFalse, FStar_ToSMT_Term.mkFalse)
end)
end)

# 22 "FStar.ToSMT.SplitQueryCases.fst"
let rec is_ite_all_the_way : Prims.int  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term Prims.list  ->  (Prims.bool * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (_39_27) -> begin
(let _118_31 = (let _118_30 = (let _118_29 = (FStar_ToSMT_Term.mkNot t)
in (negs, _118_29))
in (FStar_ToSMT_Term.mkAnd _118_30))
in (true, l, _118_31))
end
| _39_30 -> begin
(
# 29 "FStar.ToSMT.SplitQueryCases.fst"
let _39_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_39_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _118_34 = (let _118_33 = (FStar_ToSMT_Term.mkImp (negs, t))
in (_118_33)::l)
in (is_ite_all_the_way n rest negs' _118_34))
end else begin
(false, [], FStar_ToSMT_Term.mkFalse)
end
end))
end)
end)

# 36 "FStar.ToSMT.SplitQueryCases.fst"
let rec parse_query_for_split_cases : Prims.int  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  (Prims.bool * ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)) = (fun n t f -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _118_61 = (FStar_ToSMT_Term.mkForall'' (l, opt, l', x))
in (f _118_61))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, t1::t2::_39_50) -> begin
(
# 41 "FStar.ToSMT.SplitQueryCases.fst"
let r = (match (t2.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, _39_59, _39_61, _39_63, _39_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _118_69 = (FStar_ToSMT_Term.mkImp (t1, x))
in (f _118_69))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _39_71) -> begin
(
# 47 "FStar.ToSMT.SplitQueryCases.fst"
let _39_77 = (is_ite_all_the_way n t2 FStar_ToSMT_Term.mkTrue [])
in (match (_39_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _118_78 = (FStar_ToSMT_Term.mkImp (t1, x))
in (f _118_78))), l, negs))
end))
end
| _39_80 -> begin
(false, ((fun _39_81 -> FStar_ToSMT_Term.mkFalse), [], FStar_ToSMT_Term.mkFalse))
end)
in r)
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _39_86) -> begin
(
# 55 "FStar.ToSMT.SplitQueryCases.fst"
let _39_92 = (is_ite_all_the_way n t FStar_ToSMT_Term.mkTrue [])
in (match (_39_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _39_94 -> begin
(false, ((fun _39_95 -> FStar_ToSMT_Term.mkFalse), [], FStar_ToSMT_Term.mkFalse))
end))

# 60 "FStar.ToSMT.SplitQueryCases.fst"
let strip_not : FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term = (fun t -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Not, hd::_39_100) -> begin
hd
end
| _39_106 -> begin
t
end))

# 64 "FStar.ToSMT.SplitQueryCases.fst"
let rec check_split_cases : (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term Prims.list  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _118_117 = (let _118_116 = (let _118_115 = (let _118_114 = (f t)
in (FStar_ToSMT_Term.mkNot _118_114))
in (_118_115, None))
in FStar_ToSMT_Term.Assume (_118_116))
in (check _118_117))) (FStar_List.rev l)))

# 67 "FStar.ToSMT.SplitQueryCases.fst"
let check_exhaustiveness : (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _118_138 = (let _118_137 = (let _118_136 = (let _118_135 = (let _118_134 = (FStar_ToSMT_Term.mkNot negs)
in (f _118_134))
in (FStar_ToSMT_Term.mkNot _118_135))
in (_118_136, None))
in FStar_ToSMT_Term.Assume (_118_137))
in (check _118_138)))

# 70 "FStar.ToSMT.SplitQueryCases.fst"
let can_handle_query : Prims.int  ->  FStar_ToSMT_Term.decl  ->  (Prims.bool * ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)) = (fun n q -> (match (q) with
| FStar_ToSMT_Term.Assume (q', _39_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _39_123 -> begin
(false, ((fun x -> x), [], FStar_ToSMT_Term.mkFalse))
end))

# 75 "FStar.ToSMT.SplitQueryCases.fst"
let handle_query : ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _39_128 check -> (match (_39_128) with
| (f, l, negs) -> begin
(
# 76 "FStar.ToSMT.SplitQueryCases.fst"
let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





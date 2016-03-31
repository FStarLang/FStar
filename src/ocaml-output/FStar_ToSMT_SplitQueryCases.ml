
open Prims
# 10 "FStar.ToSMT.SplitQueryCases.fst"
let rec get_next_n_ite : Prims.int  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  (Prims.bool * FStar_ToSMT_Term.term * FStar_ToSMT_Term.term * FStar_ToSMT_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _138_14 = (f FStar_ToSMT_Term.mkTrue)
in (true, _138_14, negs, t))
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, g::t::e::_49_7) -> begin
(let _138_19 = (let _138_16 = (let _138_15 = (FStar_ToSMT_Term.mkNot g)
in (negs, _138_15))
in (FStar_ToSMT_Term.mkAnd _138_16))
in (get_next_n_ite (n - 1) e _138_19 (fun x -> (let _138_18 = (FStar_ToSMT_Term.mkITE (g, t, x))
in (f _138_18)))))
end
| FStar_ToSMT_Term.FreeV (_49_18) -> begin
(let _138_20 = (f FStar_ToSMT_Term.mkTrue)
in (true, _138_20, negs, t))
end
| _49_21 -> begin
(false, FStar_ToSMT_Term.mkFalse, FStar_ToSMT_Term.mkFalse, FStar_ToSMT_Term.mkFalse)
end)
end)

# 22 "FStar.ToSMT.SplitQueryCases.fst"
let rec is_ite_all_the_way : Prims.int  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term Prims.list  ->  (Prims.bool * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (_49_27) -> begin
(let _138_31 = (let _138_30 = (let _138_29 = (FStar_ToSMT_Term.mkNot t)
in (negs, _138_29))
in (FStar_ToSMT_Term.mkAnd _138_30))
in (true, l, _138_31))
end
| _49_30 -> begin
(
# 29 "FStar.ToSMT.SplitQueryCases.fst"
let _49_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_49_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _138_34 = (let _138_33 = (FStar_ToSMT_Term.mkImp (negs, t))
in (_138_33)::l)
in (is_ite_all_the_way n rest negs' _138_34))
end else begin
(false, [], FStar_ToSMT_Term.mkFalse)
end
end))
end)
end)

# 36 "FStar.ToSMT.SplitQueryCases.fst"
let rec parse_query_for_split_cases : Prims.int  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  (Prims.bool * ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)) = (fun n t f -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _138_61 = (FStar_ToSMT_Term.mkForall'' (l, opt, l', x))
in (f _138_61))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, t1::t2::_49_50) -> begin
(
# 41 "FStar.ToSMT.SplitQueryCases.fst"
let r = (match (t2.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, _49_59, _49_61, _49_63, _49_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _138_69 = (FStar_ToSMT_Term.mkImp (t1, x))
in (f _138_69))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _49_71) -> begin
(
# 47 "FStar.ToSMT.SplitQueryCases.fst"
let _49_77 = (is_ite_all_the_way n t2 FStar_ToSMT_Term.mkTrue [])
in (match (_49_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _138_78 = (FStar_ToSMT_Term.mkImp (t1, x))
in (f _138_78))), l, negs))
end))
end
| _49_80 -> begin
(false, ((fun _49_81 -> FStar_ToSMT_Term.mkFalse), [], FStar_ToSMT_Term.mkFalse))
end)
in r)
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _49_86) -> begin
(
# 55 "FStar.ToSMT.SplitQueryCases.fst"
let _49_92 = (is_ite_all_the_way n t FStar_ToSMT_Term.mkTrue [])
in (match (_49_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _49_94 -> begin
(false, ((fun _49_95 -> FStar_ToSMT_Term.mkFalse), [], FStar_ToSMT_Term.mkFalse))
end))

# 60 "FStar.ToSMT.SplitQueryCases.fst"
let strip_not : FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term = (fun t -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Not, hd::_49_100) -> begin
hd
end
| _49_106 -> begin
t
end))

# 64 "FStar.ToSMT.SplitQueryCases.fst"
let rec check_split_cases : (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term Prims.list  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _138_117 = (let _138_116 = (let _138_115 = (let _138_114 = (f t)
in (FStar_ToSMT_Term.mkNot _138_114))
in (_138_115, None))
in FStar_ToSMT_Term.Assume (_138_116))
in (check _138_117))) (FStar_List.rev l)))

# 67 "FStar.ToSMT.SplitQueryCases.fst"
let check_exhaustiveness : (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _138_138 = (let _138_137 = (let _138_136 = (let _138_135 = (let _138_134 = (FStar_ToSMT_Term.mkNot negs)
in (f _138_134))
in (FStar_ToSMT_Term.mkNot _138_135))
in (_138_136, None))
in FStar_ToSMT_Term.Assume (_138_137))
in (check _138_138)))

# 70 "FStar.ToSMT.SplitQueryCases.fst"
let can_handle_query : Prims.int  ->  FStar_ToSMT_Term.decl  ->  (Prims.bool * ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)) = (fun n q -> (match (q) with
| FStar_ToSMT_Term.Assume (q', _49_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _49_123 -> begin
(false, ((fun x -> x), [], FStar_ToSMT_Term.mkFalse))
end))

# 75 "FStar.ToSMT.SplitQueryCases.fst"
let handle_query : ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _49_128 check -> (match (_49_128) with
| (f, l, negs) -> begin
(
# 76 "FStar.ToSMT.SplitQueryCases.fst"
let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





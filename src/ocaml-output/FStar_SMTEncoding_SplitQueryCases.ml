
open Prims
# 22 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _170_14 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _170_14, negs, t))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, g::t::e::_81_7) -> begin
(let _170_19 = (let _170_16 = (let _170_15 = (FStar_SMTEncoding_Term.mkNot g)
in (negs, _170_15))
in (FStar_SMTEncoding_Term.mkAnd _170_16))
in (get_next_n_ite (n - 1) e _170_19 (fun x -> (let _170_18 = (FStar_SMTEncoding_Term.mkITE (g, t, x))
in (f _170_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_81_18) -> begin
(let _170_20 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _170_20, negs, t))
end
| _81_21 -> begin
(false, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse)
end)
end)

# 34 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_81_27) -> begin
(let _170_31 = (let _170_30 = (let _170_29 = (FStar_SMTEncoding_Term.mkNot t)
in (negs, _170_29))
in (FStar_SMTEncoding_Term.mkAnd _170_30))
in (true, l, _170_31))
end
| _81_30 -> begin
(
# 44 "FStar.SMTEncoding.SplitQueryCases.fst"
let _81_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_81_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _170_34 = (let _170_33 = (FStar_SMTEncoding_Term.mkImp (negs, t))
in (_170_33)::l)
in (is_ite_all_the_way n rest negs' _170_34))
end else begin
(false, [], FStar_SMTEncoding_Term.mkFalse)
end
end))
end)
end)

# 48 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _170_61 = (FStar_SMTEncoding_Term.mkForall'' (l, opt, l', x))
in (f _170_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, t1::t2::_81_50) -> begin
(
# 56 "FStar.SMTEncoding.SplitQueryCases.fst"
let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _81_59, _81_61, _81_63, _81_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _170_69 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _170_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _81_71) -> begin
(
# 62 "FStar.SMTEncoding.SplitQueryCases.fst"
let _81_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Term.mkTrue [])
in (match (_81_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _170_78 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _170_78))), l, negs))
end))
end
| _81_80 -> begin
(false, ((fun _81_81 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _81_86) -> begin
(
# 70 "FStar.SMTEncoding.SplitQueryCases.fst"
let _81_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Term.mkTrue [])
in (match (_81_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _81_94 -> begin
(false, ((fun _81_95 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end))

# 73 "FStar.SMTEncoding.SplitQueryCases.fst"
let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, hd::_81_100) -> begin
hd
end
| _81_106 -> begin
t
end))

# 77 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _170_117 = (let _170_116 = (let _170_115 = (let _170_114 = (f t)
in (FStar_SMTEncoding_Term.mkNot _170_114))
in (_170_115, None))
in FStar_SMTEncoding_Term.Assume (_170_116))
in (check _170_117))) (FStar_List.rev l)))

# 80 "FStar.SMTEncoding.SplitQueryCases.fst"
let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _170_138 = (let _170_137 = (let _170_136 = (let _170_135 = (let _170_134 = (FStar_SMTEncoding_Term.mkNot negs)
in (f _170_134))
in (FStar_SMTEncoding_Term.mkNot _170_135))
in (_170_136, None))
in FStar_SMTEncoding_Term.Assume (_170_137))
in (check _170_138)))

# 83 "FStar.SMTEncoding.SplitQueryCases.fst"
let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _81_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _81_123 -> begin
(false, ((fun x -> x), [], FStar_SMTEncoding_Term.mkFalse))
end))

# 88 "FStar.SMTEncoding.SplitQueryCases.fst"
let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _81_128 check -> (match (_81_128) with
| (f, l, negs) -> begin
(
# 91 "FStar.SMTEncoding.SplitQueryCases.fst"
let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





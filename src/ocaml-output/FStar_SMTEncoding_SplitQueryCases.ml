
open Prims
# 22 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _153_14 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _153_14, negs, t))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, g::t::e::_72_7) -> begin
(let _153_19 = (let _153_16 = (let _153_15 = (FStar_SMTEncoding_Term.mkNot g)
in (negs, _153_15))
in (FStar_SMTEncoding_Term.mkAnd _153_16))
in (get_next_n_ite (n - 1) e _153_19 (fun x -> (let _153_18 = (FStar_SMTEncoding_Term.mkITE (g, t, x))
in (f _153_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_72_18) -> begin
(let _153_20 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _153_20, negs, t))
end
| _72_21 -> begin
(false, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse)
end)
end)

# 34 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_72_27) -> begin
(let _153_31 = (let _153_30 = (let _153_29 = (FStar_SMTEncoding_Term.mkNot t)
in (negs, _153_29))
in (FStar_SMTEncoding_Term.mkAnd _153_30))
in (true, l, _153_31))
end
| _72_30 -> begin
(
# 44 "FStar.SMTEncoding.SplitQueryCases.fst"
let _72_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_72_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _153_34 = (let _153_33 = (FStar_SMTEncoding_Term.mkImp (negs, t))
in (_153_33)::l)
in (is_ite_all_the_way n rest negs' _153_34))
end else begin
(false, [], FStar_SMTEncoding_Term.mkFalse)
end
end))
end)
end)

# 48 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _153_61 = (FStar_SMTEncoding_Term.mkForall'' (l, opt, l', x))
in (f _153_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, t1::t2::_72_50) -> begin
(
# 56 "FStar.SMTEncoding.SplitQueryCases.fst"
let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _72_59, _72_61, _72_63, _72_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _153_69 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _153_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _72_71) -> begin
(
# 62 "FStar.SMTEncoding.SplitQueryCases.fst"
let _72_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Term.mkTrue [])
in (match (_72_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _153_78 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _153_78))), l, negs))
end))
end
| _72_80 -> begin
(false, ((fun _72_81 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _72_86) -> begin
(
# 70 "FStar.SMTEncoding.SplitQueryCases.fst"
let _72_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Term.mkTrue [])
in (match (_72_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _72_94 -> begin
(false, ((fun _72_95 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end))

# 73 "FStar.SMTEncoding.SplitQueryCases.fst"
let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, hd::_72_100) -> begin
hd
end
| _72_106 -> begin
t
end))

# 77 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _153_117 = (let _153_116 = (let _153_115 = (let _153_114 = (f t)
in (FStar_SMTEncoding_Term.mkNot _153_114))
in (_153_115, None))
in FStar_SMTEncoding_Term.Assume (_153_116))
in (check _153_117))) (FStar_List.rev l)))

# 80 "FStar.SMTEncoding.SplitQueryCases.fst"
let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _153_138 = (let _153_137 = (let _153_136 = (let _153_135 = (let _153_134 = (FStar_SMTEncoding_Term.mkNot negs)
in (f _153_134))
in (FStar_SMTEncoding_Term.mkNot _153_135))
in (_153_136, None))
in FStar_SMTEncoding_Term.Assume (_153_137))
in (check _153_138)))

# 83 "FStar.SMTEncoding.SplitQueryCases.fst"
let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _72_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _72_123 -> begin
(false, ((fun x -> x), [], FStar_SMTEncoding_Term.mkFalse))
end))

# 88 "FStar.SMTEncoding.SplitQueryCases.fst"
let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _72_128 check -> (match (_72_128) with
| (f, l, negs) -> begin
(
# 91 "FStar.SMTEncoding.SplitQueryCases.fst"
let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





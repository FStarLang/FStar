
open Prims
# 25 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _155_14 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _155_14, negs, t))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, g::t::e::_73_7) -> begin
(let _155_19 = (let _155_16 = (let _155_15 = (FStar_SMTEncoding_Term.mkNot g)
in (negs, _155_15))
in (FStar_SMTEncoding_Term.mkAnd _155_16))
in (get_next_n_ite (n - 1) e _155_19 (fun x -> (let _155_18 = (FStar_SMTEncoding_Term.mkITE (g, t, x))
in (f _155_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_73_18) -> begin
(let _155_20 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _155_20, negs, t))
end
| _73_21 -> begin
(false, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse)
end)
end)

# 37 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_73_27) -> begin
(let _155_31 = (let _155_30 = (let _155_29 = (FStar_SMTEncoding_Term.mkNot t)
in (negs, _155_29))
in (FStar_SMTEncoding_Term.mkAnd _155_30))
in (true, l, _155_31))
end
| _73_30 -> begin
(
# 44 "FStar.SMTEncoding.SplitQueryCases.fst"
let _73_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_73_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _155_34 = (let _155_33 = (FStar_SMTEncoding_Term.mkImp (negs, t))
in (_155_33)::l)
in (is_ite_all_the_way n rest negs' _155_34))
end else begin
(false, [], FStar_SMTEncoding_Term.mkFalse)
end
end))
end)
end)

# 51 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _155_61 = (FStar_SMTEncoding_Term.mkForall'' (l, opt, l', x))
in (f _155_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, t1::t2::_73_50) -> begin
(
# 56 "FStar.SMTEncoding.SplitQueryCases.fst"
let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _73_59, _73_61, _73_63, _73_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _155_69 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _155_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _73_71) -> begin
(
# 62 "FStar.SMTEncoding.SplitQueryCases.fst"
let _73_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Term.mkTrue [])
in (match (_73_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _155_78 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _155_78))), l, negs))
end))
end
| _73_80 -> begin
(false, ((fun _73_81 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _73_86) -> begin
(
# 70 "FStar.SMTEncoding.SplitQueryCases.fst"
let _73_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Term.mkTrue [])
in (match (_73_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _73_94 -> begin
(false, ((fun _73_95 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end))

# 75 "FStar.SMTEncoding.SplitQueryCases.fst"
let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, hd::_73_100) -> begin
hd
end
| _73_106 -> begin
t
end))

# 79 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _155_117 = (let _155_116 = (let _155_115 = (let _155_114 = (f t)
in (FStar_SMTEncoding_Term.mkNot _155_114))
in (_155_115, None))
in FStar_SMTEncoding_Term.Assume (_155_116))
in (check _155_117))) (FStar_List.rev l)))

# 82 "FStar.SMTEncoding.SplitQueryCases.fst"
let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _155_138 = (let _155_137 = (let _155_136 = (let _155_135 = (let _155_134 = (FStar_SMTEncoding_Term.mkNot negs)
in (f _155_134))
in (FStar_SMTEncoding_Term.mkNot _155_135))
in (_155_136, None))
in FStar_SMTEncoding_Term.Assume (_155_137))
in (check _155_138)))

# 85 "FStar.SMTEncoding.SplitQueryCases.fst"
let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _73_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _73_123 -> begin
(false, ((fun x -> x), [], FStar_SMTEncoding_Term.mkFalse))
end))

# 90 "FStar.SMTEncoding.SplitQueryCases.fst"
let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _73_128 check -> (match (_73_128) with
| (f, l, negs) -> begin
(
# 91 "FStar.SMTEncoding.SplitQueryCases.fst"
let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





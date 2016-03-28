
open Prims
# 22 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _162_14 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _162_14, negs, t))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, g::t::e::_77_7) -> begin
(let _162_19 = (let _162_16 = (let _162_15 = (FStar_SMTEncoding_Term.mkNot g)
in (negs, _162_15))
in (FStar_SMTEncoding_Term.mkAnd _162_16))
in (get_next_n_ite (n - 1) e _162_19 (fun x -> (let _162_18 = (FStar_SMTEncoding_Term.mkITE (g, t, x))
in (f _162_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_77_18) -> begin
(let _162_20 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _162_20, negs, t))
end
| _77_21 -> begin
(false, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse)
end)
end)

# 34 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_77_27) -> begin
(let _162_31 = (let _162_30 = (let _162_29 = (FStar_SMTEncoding_Term.mkNot t)
in (negs, _162_29))
in (FStar_SMTEncoding_Term.mkAnd _162_30))
in (true, l, _162_31))
end
| _77_30 -> begin
(
# 44 "FStar.SMTEncoding.SplitQueryCases.fst"
let _77_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_77_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _162_34 = (let _162_33 = (FStar_SMTEncoding_Term.mkImp (negs, t))
in (_162_33)::l)
in (is_ite_all_the_way n rest negs' _162_34))
end else begin
(false, [], FStar_SMTEncoding_Term.mkFalse)
end
end))
end)
end)

# 48 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _162_61 = (FStar_SMTEncoding_Term.mkForall'' (l, opt, l', x))
in (f _162_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, t1::t2::_77_50) -> begin
(
# 56 "FStar.SMTEncoding.SplitQueryCases.fst"
let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _77_59, _77_61, _77_63, _77_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _162_69 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _162_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _77_71) -> begin
(
# 62 "FStar.SMTEncoding.SplitQueryCases.fst"
let _77_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Term.mkTrue [])
in (match (_77_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _162_78 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _162_78))), l, negs))
end))
end
| _77_80 -> begin
(false, ((fun _77_81 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _77_86) -> begin
(
# 70 "FStar.SMTEncoding.SplitQueryCases.fst"
let _77_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Term.mkTrue [])
in (match (_77_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _77_94 -> begin
(false, ((fun _77_95 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end))

# 73 "FStar.SMTEncoding.SplitQueryCases.fst"
let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, hd::_77_100) -> begin
hd
end
| _77_106 -> begin
t
end))

# 77 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _162_117 = (let _162_116 = (let _162_115 = (let _162_114 = (f t)
in (FStar_SMTEncoding_Term.mkNot _162_114))
in (_162_115, None))
in FStar_SMTEncoding_Term.Assume (_162_116))
in (check _162_117))) (FStar_List.rev l)))

# 80 "FStar.SMTEncoding.SplitQueryCases.fst"
let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _162_138 = (let _162_137 = (let _162_136 = (let _162_135 = (let _162_134 = (FStar_SMTEncoding_Term.mkNot negs)
in (f _162_134))
in (FStar_SMTEncoding_Term.mkNot _162_135))
in (_162_136, None))
in FStar_SMTEncoding_Term.Assume (_162_137))
in (check _162_138)))

# 83 "FStar.SMTEncoding.SplitQueryCases.fst"
let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _77_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _77_123 -> begin
(false, ((fun x -> x), [], FStar_SMTEncoding_Term.mkFalse))
end))

# 88 "FStar.SMTEncoding.SplitQueryCases.fst"
let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _77_128 check -> (match (_77_128) with
| (f, l, negs) -> begin
(
# 91 "FStar.SMTEncoding.SplitQueryCases.fst"
let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





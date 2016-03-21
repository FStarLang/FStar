
open Prims
# 25 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _160_14 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _160_14, negs, t))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, g::t::e::_76_7) -> begin
(let _160_19 = (let _160_16 = (let _160_15 = (FStar_SMTEncoding_Term.mkNot g)
in (negs, _160_15))
in (FStar_SMTEncoding_Term.mkAnd _160_16))
in (get_next_n_ite (n - 1) e _160_19 (fun x -> (let _160_18 = (FStar_SMTEncoding_Term.mkITE (g, t, x))
in (f _160_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_76_18) -> begin
(let _160_20 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _160_20, negs, t))
end
| _76_21 -> begin
(false, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse)
end)
end)

# 37 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_76_27) -> begin
(let _160_31 = (let _160_30 = (let _160_29 = (FStar_SMTEncoding_Term.mkNot t)
in (negs, _160_29))
in (FStar_SMTEncoding_Term.mkAnd _160_30))
in (true, l, _160_31))
end
| _76_30 -> begin
(
# 44 "FStar.SMTEncoding.SplitQueryCases.fst"
let _76_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_76_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _160_34 = (let _160_33 = (FStar_SMTEncoding_Term.mkImp (negs, t))
in (_160_33)::l)
in (is_ite_all_the_way n rest negs' _160_34))
end else begin
(false, [], FStar_SMTEncoding_Term.mkFalse)
end
end))
end)
end)

# 51 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _160_61 = (FStar_SMTEncoding_Term.mkForall'' (l, opt, l', x))
in (f _160_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, t1::t2::_76_50) -> begin
(
# 56 "FStar.SMTEncoding.SplitQueryCases.fst"
let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _76_59, _76_61, _76_63, _76_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _160_69 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _160_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _76_71) -> begin
(
# 62 "FStar.SMTEncoding.SplitQueryCases.fst"
let _76_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Term.mkTrue [])
in (match (_76_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _160_78 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _160_78))), l, negs))
end))
end
| _76_80 -> begin
(false, ((fun _76_81 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _76_86) -> begin
(
# 70 "FStar.SMTEncoding.SplitQueryCases.fst"
let _76_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Term.mkTrue [])
in (match (_76_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _76_94 -> begin
(false, ((fun _76_95 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end))

# 75 "FStar.SMTEncoding.SplitQueryCases.fst"
let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, hd::_76_100) -> begin
hd
end
| _76_106 -> begin
t
end))

# 79 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _160_117 = (let _160_116 = (let _160_115 = (let _160_114 = (f t)
in (FStar_SMTEncoding_Term.mkNot _160_114))
in (_160_115, None))
in FStar_SMTEncoding_Term.Assume (_160_116))
in (check _160_117))) (FStar_List.rev l)))

# 82 "FStar.SMTEncoding.SplitQueryCases.fst"
let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _160_138 = (let _160_137 = (let _160_136 = (let _160_135 = (let _160_134 = (FStar_SMTEncoding_Term.mkNot negs)
in (f _160_134))
in (FStar_SMTEncoding_Term.mkNot _160_135))
in (_160_136, None))
in FStar_SMTEncoding_Term.Assume (_160_137))
in (check _160_138)))

# 85 "FStar.SMTEncoding.SplitQueryCases.fst"
let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _76_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _76_123 -> begin
(false, ((fun x -> x), [], FStar_SMTEncoding_Term.mkFalse))
end))

# 90 "FStar.SMTEncoding.SplitQueryCases.fst"
let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _76_128 check -> (match (_76_128) with
| (f, l, negs) -> begin
(
# 91 "FStar.SMTEncoding.SplitQueryCases.fst"
let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





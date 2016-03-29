
open Prims
# 25 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _150_14 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _150_14, negs, t))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, g::t::e::_71_7) -> begin
(let _150_19 = (let _150_16 = (let _150_15 = (FStar_SMTEncoding_Term.mkNot g)
in (negs, _150_15))
in (FStar_SMTEncoding_Term.mkAnd _150_16))
in (get_next_n_ite (n - 1) e _150_19 (fun x -> (let _150_18 = (FStar_SMTEncoding_Term.mkITE (g, t, x))
in (f _150_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_71_18) -> begin
(let _150_20 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _150_20, negs, t))
end
| _71_21 -> begin
(false, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse)
end)
end)

# 37 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_71_27) -> begin
(let _150_31 = (let _150_30 = (let _150_29 = (FStar_SMTEncoding_Term.mkNot t)
in (negs, _150_29))
in (FStar_SMTEncoding_Term.mkAnd _150_30))
in (true, l, _150_31))
end
| _71_30 -> begin
(
# 44 "FStar.SMTEncoding.SplitQueryCases.fst"
let _71_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_71_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _150_34 = (let _150_33 = (FStar_SMTEncoding_Term.mkImp (negs, t))
in (_150_33)::l)
in (is_ite_all_the_way n rest negs' _150_34))
end else begin
(false, [], FStar_SMTEncoding_Term.mkFalse)
end
end))
end)
end)

# 51 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _150_61 = (FStar_SMTEncoding_Term.mkForall'' (l, opt, l', x))
in (f _150_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, t1::t2::_71_50) -> begin
(
# 56 "FStar.SMTEncoding.SplitQueryCases.fst"
let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _71_59, _71_61, _71_63, _71_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _150_69 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _150_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _71_71) -> begin
(
# 62 "FStar.SMTEncoding.SplitQueryCases.fst"
let _71_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Term.mkTrue [])
in (match (_71_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _150_78 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _150_78))), l, negs))
end))
end
| _71_80 -> begin
(false, ((fun _71_81 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _71_86) -> begin
(
# 70 "FStar.SMTEncoding.SplitQueryCases.fst"
let _71_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Term.mkTrue [])
in (match (_71_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _71_94 -> begin
(false, ((fun _71_95 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end))

# 75 "FStar.SMTEncoding.SplitQueryCases.fst"
let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, hd::_71_100) -> begin
hd
end
| _71_106 -> begin
t
end))

# 79 "FStar.SMTEncoding.SplitQueryCases.fst"
let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _150_117 = (let _150_116 = (let _150_115 = (let _150_114 = (f t)
in (FStar_SMTEncoding_Term.mkNot _150_114))
in (_150_115, None))
in FStar_SMTEncoding_Term.Assume (_150_116))
in (check _150_117))) (FStar_List.rev l)))

# 82 "FStar.SMTEncoding.SplitQueryCases.fst"
let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _150_138 = (let _150_137 = (let _150_136 = (let _150_135 = (let _150_134 = (FStar_SMTEncoding_Term.mkNot negs)
in (f _150_134))
in (FStar_SMTEncoding_Term.mkNot _150_135))
in (_150_136, None))
in FStar_SMTEncoding_Term.Assume (_150_137))
in (check _150_138)))

# 85 "FStar.SMTEncoding.SplitQueryCases.fst"
let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _71_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _71_123 -> begin
(false, ((fun x -> x), [], FStar_SMTEncoding_Term.mkFalse))
end))

# 90 "FStar.SMTEncoding.SplitQueryCases.fst"
let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _71_128 check -> (match (_71_128) with
| (f, l, negs) -> begin
(
# 91 "FStar.SMTEncoding.SplitQueryCases.fst"
let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





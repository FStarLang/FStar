
open Prims
# 25 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\splitcases.fs"

let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _199_14 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _199_14, negs, t))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, g::t::e::_97_7) -> begin
(let _199_19 = (let _199_16 = (let _199_15 = (FStar_SMTEncoding_Term.mkNot g)
in (negs, _199_15))
in (FStar_SMTEncoding_Term.mkAnd _199_16))
in (get_next_n_ite (n - 1) e _199_19 (fun x -> (let _199_18 = (FStar_SMTEncoding_Term.mkITE (g, t, x))
in (f _199_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_97_18) -> begin
(let _199_20 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _199_20, negs, t))
end
| _97_21 -> begin
(false, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse)
end)
end)

# 37 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\splitcases.fs"

let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_97_27) -> begin
(let _199_31 = (let _199_30 = (let _199_29 = (FStar_SMTEncoding_Term.mkNot t)
in (negs, _199_29))
in (FStar_SMTEncoding_Term.mkAnd _199_30))
in (true, l, _199_31))
end
| _97_30 -> begin
(let _97_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_97_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _199_34 = (let _199_33 = (FStar_SMTEncoding_Term.mkImp (negs, t))
in (_199_33)::l)
in (is_ite_all_the_way n rest negs' _199_34))
end else begin
(false, [], FStar_SMTEncoding_Term.mkFalse)
end
end))
end)
end)

# 51 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\splitcases.fs"

let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _199_61 = (FStar_SMTEncoding_Term.mkForall'' (l, opt, l', x))
in (f _199_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, t1::t2::_97_50) -> begin
(let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _97_59, _97_61, _97_63, _97_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _199_69 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _199_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _97_71) -> begin
(let _97_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Term.mkTrue [])
in (match (_97_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _199_78 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _199_78))), l, negs))
end))
end
| _97_80 -> begin
(false, ((fun _97_81 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _97_86) -> begin
(let _97_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Term.mkTrue [])
in (match (_97_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _97_94 -> begin
(false, ((fun _97_95 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end))

# 75 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\splitcases.fs"

let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, hd::_97_100) -> begin
hd
end
| _97_106 -> begin
t
end))

# 79 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\splitcases.fs"

let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _199_117 = (let _199_116 = (let _199_115 = (let _199_114 = (f t)
in (FStar_SMTEncoding_Term.mkNot _199_114))
in (_199_115, None))
in FStar_SMTEncoding_Term.Assume (_199_116))
in (check _199_117))) (FStar_List.rev l)))

# 82 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\splitcases.fs"

let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _199_138 = (let _199_137 = (let _199_136 = (let _199_135 = (let _199_134 = (FStar_SMTEncoding_Term.mkNot negs)
in (f _199_134))
in (FStar_SMTEncoding_Term.mkNot _199_135))
in (_199_136, None))
in FStar_SMTEncoding_Term.Assume (_199_137))
in (check _199_138)))

# 85 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\splitcases.fs"

let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _97_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _97_123 -> begin
(false, ((fun x -> x), [], FStar_SMTEncoding_Term.mkFalse))
end))

# 90 "C:\\Users\\nswamy\\workspace\\FStar\\src\\smtencoding\\splitcases.fs"

let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _97_128 check -> (match (_97_128) with
| (f, l, negs) -> begin
(let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





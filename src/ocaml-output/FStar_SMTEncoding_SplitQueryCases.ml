
open Prims

let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _171_14 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _171_14, negs, t))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (g)::(t)::(e)::_81_7) -> begin
(let _171_19 = (let _171_16 = (let _171_15 = (FStar_SMTEncoding_Term.mkNot g)
in (negs, _171_15))
in (FStar_SMTEncoding_Term.mkAnd _171_16))
in (get_next_n_ite (n - 1) e _171_19 (fun x -> (let _171_18 = (FStar_SMTEncoding_Term.mkITE (g, t, x))
in (f _171_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_81_18) -> begin
(let _171_20 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _171_20, negs, t))
end
| _81_21 -> begin
(false, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse)
end)
end)


let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_81_27) -> begin
(let _171_31 = (let _171_30 = (let _171_29 = (FStar_SMTEncoding_Term.mkNot t)
in (negs, _171_29))
in (FStar_SMTEncoding_Term.mkAnd _171_30))
in (true, l, _171_31))
end
| _81_30 -> begin
(

let _81_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_81_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _171_34 = (let _171_33 = (FStar_SMTEncoding_Term.mkImp (negs, t))
in (_171_33)::l)
in (is_ite_all_the_way n rest negs' _171_34))
end else begin
(false, [], FStar_SMTEncoding_Term.mkFalse)
end
end))
end)
end)


let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _171_61 = (FStar_SMTEncoding_Term.mkForall'' (l, opt, l', x))
in (f _171_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (t1)::(t2)::_81_50) -> begin
(

let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _81_59, _81_61, _81_63, _81_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _171_69 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _171_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _81_71) -> begin
(

let _81_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Term.mkTrue [])
in (match (_81_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _171_78 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _171_78))), l, negs))
end))
end
| _81_80 -> begin
(false, ((fun _81_81 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _81_86) -> begin
(

let _81_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Term.mkTrue [])
in (match (_81_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _81_94 -> begin
(false, ((fun _81_95 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end))


let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, (hd)::_81_100) -> begin
hd
end
| _81_106 -> begin
t
end))


let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _171_117 = (let _171_116 = (let _171_115 = (let _171_114 = (f t)
in (FStar_SMTEncoding_Term.mkNot _171_114))
in (_171_115, None, None))
in FStar_SMTEncoding_Term.Assume (_171_116))
in (check _171_117))) (FStar_List.rev l)))


let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _171_138 = (let _171_137 = (let _171_136 = (let _171_135 = (let _171_134 = (FStar_SMTEncoding_Term.mkNot negs)
in (f _171_134))
in (FStar_SMTEncoding_Term.mkNot _171_135))
in (_171_136, None, None))
in FStar_SMTEncoding_Term.Assume (_171_137))
in (check _171_138)))


let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _81_118, _81_120) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _81_125 -> begin
(false, ((fun x -> x), [], FStar_SMTEncoding_Term.mkFalse))
end))


let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _81_130 check -> (match (_81_130) with
| (f, l, negs) -> begin
(

let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





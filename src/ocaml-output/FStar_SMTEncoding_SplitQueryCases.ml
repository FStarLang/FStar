
open Prims

let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= (Prims.parse_int "0")) then begin
(let _179_14 = (f FStar_SMTEncoding_Term.mkTrue)
in ((true), (_179_14), (negs), (t)))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (g)::(t)::(e)::_85_7) -> begin
(let _179_19 = (let _179_16 = (let _179_15 = (FStar_SMTEncoding_Term.mkNot g)
in ((negs), (_179_15)))
in (FStar_SMTEncoding_Term.mkAnd _179_16))
in (get_next_n_ite (n - (Prims.parse_int "1")) e _179_19 (fun x -> (let _179_18 = (FStar_SMTEncoding_Term.mkITE ((g), (t), (x)))
in (f _179_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_85_18) -> begin
(let _179_20 = (f FStar_SMTEncoding_Term.mkTrue)
in ((true), (_179_20), (negs), (t)))
end
| _85_21 -> begin
((false), (FStar_SMTEncoding_Term.mkFalse), (FStar_SMTEncoding_Term.mkFalse), (FStar_SMTEncoding_Term.mkFalse))
end)
end)


let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= (Prims.parse_int "0")) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_85_27) -> begin
(let _179_31 = (let _179_30 = (let _179_29 = (FStar_SMTEncoding_Term.mkNot t)
in ((negs), (_179_29)))
in (FStar_SMTEncoding_Term.mkAnd _179_30))
in ((true), (l), (_179_31)))
end
| _85_30 -> begin
(

let _85_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_85_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _179_34 = (let _179_33 = (FStar_SMTEncoding_Term.mkImp ((negs), (t)))
in (_179_33)::l)
in (is_ite_all_the_way n rest negs' _179_34))
end else begin
((false), ([]), (FStar_SMTEncoding_Term.mkFalse))
end
end))
end)
end)


let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _179_61 = (FStar_SMTEncoding_Term.mkForall'' ((l), (opt), (l'), (x)))
in (f _179_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (t1)::(t2)::_85_50) -> begin
(

let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _85_59, _85_61, _85_63, _85_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _179_69 = (FStar_SMTEncoding_Term.mkImp ((t1), (x)))
in (f _179_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _85_71) -> begin
(

let _85_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Term.mkTrue [])
in (match (_85_77) with
| (b, l, negs) -> begin
((b), ((((fun x -> (let _179_78 = (FStar_SMTEncoding_Term.mkImp ((t1), (x)))
in (f _179_78)))), (l), (negs))))
end))
end
| _85_80 -> begin
((false), ((((fun _85_81 -> FStar_SMTEncoding_Term.mkFalse)), ([]), (FStar_SMTEncoding_Term.mkFalse))))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _85_86) -> begin
(

let _85_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Term.mkTrue [])
in (match (_85_92) with
| (b, l, negs) -> begin
((b), (((f), (l), (negs))))
end))
end
| _85_94 -> begin
((false), ((((fun _85_95 -> FStar_SMTEncoding_Term.mkFalse)), ([]), (FStar_SMTEncoding_Term.mkFalse))))
end))


let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, (hd)::_85_100) -> begin
hd
end
| _85_106 -> begin
t
end))


let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _179_117 = (let _179_116 = (let _179_115 = (let _179_114 = (f t)
in (FStar_SMTEncoding_Term.mkNot _179_114))
in ((_179_115), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_179_116))
in (check _179_117))) (FStar_List.rev l)))


let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _179_138 = (let _179_137 = (let _179_136 = (let _179_135 = (let _179_134 = (FStar_SMTEncoding_Term.mkNot negs)
in (f _179_134))
in (FStar_SMTEncoding_Term.mkNot _179_135))
in ((_179_136), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_179_137))
in (check _179_138)))


let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _85_118, _85_120) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _85_125 -> begin
((false), ((((fun x -> x)), ([]), (FStar_SMTEncoding_Term.mkFalse))))
end))


let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _85_130 check -> (match (_85_130) with
| (f, l, negs) -> begin
(

let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





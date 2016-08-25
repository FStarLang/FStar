
open Prims

let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _177_14 = (f FStar_SMTEncoding_Term.mkTrue)
in ((true), (_177_14), (negs), (t)))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (g)::(t)::(e)::_84_7) -> begin
(let _177_19 = (let _177_16 = (let _177_15 = (FStar_SMTEncoding_Term.mkNot g)
in ((negs), (_177_15)))
in (FStar_SMTEncoding_Term.mkAnd _177_16))
in (get_next_n_ite (n - 1) e _177_19 (fun x -> (let _177_18 = (FStar_SMTEncoding_Term.mkITE ((g), (t), (x)))
in (f _177_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_84_18) -> begin
(let _177_20 = (f FStar_SMTEncoding_Term.mkTrue)
in ((true), (_177_20), (negs), (t)))
end
| _84_21 -> begin
((false), (FStar_SMTEncoding_Term.mkFalse), (FStar_SMTEncoding_Term.mkFalse), (FStar_SMTEncoding_Term.mkFalse))
end)
end)


let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_84_27) -> begin
(let _177_31 = (let _177_30 = (let _177_29 = (FStar_SMTEncoding_Term.mkNot t)
in ((negs), (_177_29)))
in (FStar_SMTEncoding_Term.mkAnd _177_30))
in ((true), (l), (_177_31)))
end
| _84_30 -> begin
(

let _84_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_84_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _177_34 = (let _177_33 = (FStar_SMTEncoding_Term.mkImp ((negs), (t)))
in (_177_33)::l)
in (is_ite_all_the_way n rest negs' _177_34))
end else begin
((false), ([]), (FStar_SMTEncoding_Term.mkFalse))
end
end))
end)
end)


let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _177_61 = (FStar_SMTEncoding_Term.mkForall'' ((l), (opt), (l'), (x)))
in (f _177_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (t1)::(t2)::_84_50) -> begin
(

let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _84_59, _84_61, _84_63, _84_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _177_69 = (FStar_SMTEncoding_Term.mkImp ((t1), (x)))
in (f _177_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _84_71) -> begin
(

let _84_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Term.mkTrue [])
in (match (_84_77) with
| (b, l, negs) -> begin
((b), ((((fun x -> (let _177_78 = (FStar_SMTEncoding_Term.mkImp ((t1), (x)))
in (f _177_78)))), (l), (negs))))
end))
end
| _84_80 -> begin
((false), ((((fun _84_81 -> FStar_SMTEncoding_Term.mkFalse)), ([]), (FStar_SMTEncoding_Term.mkFalse))))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _84_86) -> begin
(

let _84_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Term.mkTrue [])
in (match (_84_92) with
| (b, l, negs) -> begin
((b), (((f), (l), (negs))))
end))
end
| _84_94 -> begin
((false), ((((fun _84_95 -> FStar_SMTEncoding_Term.mkFalse)), ([]), (FStar_SMTEncoding_Term.mkFalse))))
end))


let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, (hd)::_84_100) -> begin
hd
end
| _84_106 -> begin
t
end))


let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _177_117 = (let _177_116 = (let _177_115 = (let _177_114 = (f t)
in (FStar_SMTEncoding_Term.mkNot _177_114))
in ((_177_115), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_177_116))
in (check _177_117))) (FStar_List.rev l)))


let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _177_138 = (let _177_137 = (let _177_136 = (let _177_135 = (let _177_134 = (FStar_SMTEncoding_Term.mkNot negs)
in (f _177_134))
in (FStar_SMTEncoding_Term.mkNot _177_135))
in ((_177_136), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_177_137))
in (check _177_138)))


let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _84_118, _84_120) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _84_125 -> begin
((false), ((((fun x -> x)), ([]), (FStar_SMTEncoding_Term.mkFalse))))
end))


let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _84_130 check -> (match (_84_130) with
| (f, l, negs) -> begin
(

let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





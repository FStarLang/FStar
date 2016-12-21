
open Prims

let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= (Prims.parse_int "0")) then begin
(let _185_14 = (f FStar_SMTEncoding_Util.mkTrue)
in ((true), (_185_14), (negs), (t)))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (g)::(t)::(e)::_88_7) -> begin
(let _185_19 = (let _185_16 = (let _185_15 = (FStar_SMTEncoding_Util.mkNot g)
in ((negs), (_185_15)))
in (FStar_SMTEncoding_Util.mkAnd _185_16))
in (get_next_n_ite (n - (Prims.parse_int "1")) e _185_19 (fun x -> (let _185_18 = (FStar_SMTEncoding_Util.mkITE ((g), (t), (x)))
in (f _185_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_88_18) -> begin
(let _185_20 = (f FStar_SMTEncoding_Util.mkTrue)
in ((true), (_185_20), (negs), (t)))
end
| _88_21 -> begin
((false), (FStar_SMTEncoding_Util.mkFalse), (FStar_SMTEncoding_Util.mkFalse), (FStar_SMTEncoding_Util.mkFalse))
end)
end)


let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= (Prims.parse_int "0")) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_88_27) -> begin
(let _185_31 = (let _185_30 = (let _185_29 = (FStar_SMTEncoding_Util.mkNot t)
in ((negs), (_185_29)))
in (FStar_SMTEncoding_Util.mkAnd _185_30))
in ((true), (l), (_185_31)))
end
| _88_30 -> begin
(

let _88_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_88_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _185_34 = (let _185_33 = (FStar_SMTEncoding_Util.mkImp ((negs), (t)))
in (_185_33)::l)
in (is_ite_all_the_way n rest negs' _185_34))
end else begin
((false), ([]), (FStar_SMTEncoding_Util.mkFalse))
end
end))
end)
end)


let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _185_61 = (FStar_SMTEncoding_Util.mkForall'' ((l), (opt), (l'), (x)))
in (f _185_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (t1)::(t2)::_88_50) -> begin
(

let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _88_59, _88_61, _88_63, _88_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _185_69 = (FStar_SMTEncoding_Util.mkImp ((t1), (x)))
in (f _185_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _88_71) -> begin
(

let _88_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Util.mkTrue [])
in (match (_88_77) with
| (b, l, negs) -> begin
((b), ((((fun x -> (let _185_78 = (FStar_SMTEncoding_Util.mkImp ((t1), (x)))
in (f _185_78)))), (l), (negs))))
end))
end
| _88_80 -> begin
((false), ((((fun _88_81 -> FStar_SMTEncoding_Util.mkFalse)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _88_86) -> begin
(

let _88_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Util.mkTrue [])
in (match (_88_92) with
| (b, l, negs) -> begin
((b), (((f), (l), (negs))))
end))
end
| _88_94 -> begin
((false), ((((fun _88_95 -> FStar_SMTEncoding_Util.mkFalse)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end))


let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, (hd)::_88_100) -> begin
hd
end
| _88_106 -> begin
t
end))


let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _185_117 = (let _185_116 = (let _185_115 = (let _185_114 = (f t)
in (FStar_SMTEncoding_Util.mkNot _185_114))
in ((_185_115), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_185_116))
in (check _185_117))) (FStar_List.rev l)))


let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _185_138 = (let _185_137 = (let _185_136 = (let _185_135 = (let _185_134 = (FStar_SMTEncoding_Util.mkNot negs)
in (f _185_134))
in (FStar_SMTEncoding_Util.mkNot _185_135))
in ((_185_136), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_185_137))
in (check _185_138)))


let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _88_118, _88_120) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _88_125 -> begin
((false), ((((fun x -> x)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end))


let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _88_130 check -> (match (_88_130) with
| (f, l, negs) -> begin
(

let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





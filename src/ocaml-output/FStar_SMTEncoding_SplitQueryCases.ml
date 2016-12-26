
open Prims

let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= (Prims.parse_int "0")) then begin
(let _191_14 = (f FStar_SMTEncoding_Util.mkTrue)
in ((true), (_191_14), (negs), (t)))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (g)::(t)::(e)::_91_7) -> begin
(let _191_19 = (let _191_16 = (let _191_15 = (FStar_SMTEncoding_Util.mkNot g)
in ((negs), (_191_15)))
in (FStar_SMTEncoding_Util.mkAnd _191_16))
in (get_next_n_ite (n - (Prims.parse_int "1")) e _191_19 (fun x -> (let _191_18 = (FStar_SMTEncoding_Util.mkITE ((g), (t), (x)))
in (f _191_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_91_18) -> begin
(let _191_20 = (f FStar_SMTEncoding_Util.mkTrue)
in ((true), (_191_20), (negs), (t)))
end
| _91_21 -> begin
((false), (FStar_SMTEncoding_Util.mkFalse), (FStar_SMTEncoding_Util.mkFalse), (FStar_SMTEncoding_Util.mkFalse))
end)
end)


let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= (Prims.parse_int "0")) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_91_27) -> begin
(let _191_31 = (let _191_30 = (let _191_29 = (FStar_SMTEncoding_Util.mkNot t)
in ((negs), (_191_29)))
in (FStar_SMTEncoding_Util.mkAnd _191_30))
in ((true), (l), (_191_31)))
end
| _91_30 -> begin
(

let _91_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_91_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _191_34 = (let _191_33 = (FStar_SMTEncoding_Util.mkImp ((negs), (t)))
in (_191_33)::l)
in (is_ite_all_the_way n rest negs' _191_34))
end else begin
((false), ([]), (FStar_SMTEncoding_Util.mkFalse))
end
end))
end)
end)


let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _191_61 = (FStar_SMTEncoding_Util.mkForall'' ((l), (opt), (l'), (x)))
in (f _191_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (t1)::(t2)::_91_50) -> begin
(

let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _91_59, _91_61, _91_63, _91_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _191_69 = (FStar_SMTEncoding_Util.mkImp ((t1), (x)))
in (f _191_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _91_71) -> begin
(

let _91_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Util.mkTrue [])
in (match (_91_77) with
| (b, l, negs) -> begin
((b), ((((fun x -> (let _191_78 = (FStar_SMTEncoding_Util.mkImp ((t1), (x)))
in (f _191_78)))), (l), (negs))))
end))
end
| _91_80 -> begin
((false), ((((fun _91_81 -> FStar_SMTEncoding_Util.mkFalse)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _91_86) -> begin
(

let _91_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Util.mkTrue [])
in (match (_91_92) with
| (b, l, negs) -> begin
((b), (((f), (l), (negs))))
end))
end
| _91_94 -> begin
((false), ((((fun _91_95 -> FStar_SMTEncoding_Util.mkFalse)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end))


let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, (hd)::_91_100) -> begin
hd
end
| _91_106 -> begin
t
end))


let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _191_117 = (let _191_116 = (let _191_115 = (let _191_114 = (f t)
in (FStar_SMTEncoding_Util.mkNot _191_114))
in ((_191_115), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_191_116))
in (check _191_117))) (FStar_List.rev l)))


let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _191_138 = (let _191_137 = (let _191_136 = (let _191_135 = (let _191_134 = (FStar_SMTEncoding_Util.mkNot negs)
in (f _191_134))
in (FStar_SMTEncoding_Util.mkNot _191_135))
in ((_191_136), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_191_137))
in (check _191_138)))


let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _91_118, _91_120) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _91_125 -> begin
((false), ((((fun x -> x)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end))


let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _91_130 check -> (match (_91_130) with
| (f, l, negs) -> begin
(

let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))





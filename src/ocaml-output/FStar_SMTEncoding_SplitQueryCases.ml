
open Prims

let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> (match ((n <= (Prims.parse_int "0"))) with
| true -> begin
(let _0_350 = (f FStar_SMTEncoding_Util.mkTrue)
in ((true), (_0_350), (negs), (t)))
end
| uu____30 -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (g)::(t)::(e)::uu____38) -> begin
(let _0_352 = (FStar_SMTEncoding_Util.mkAnd (let _0_351 = (FStar_SMTEncoding_Util.mkNot g)
in ((negs), (_0_351))))
in (get_next_n_ite (n - (Prims.parse_int "1")) e _0_352 (fun x -> (f (FStar_SMTEncoding_Util.mkITE ((g), (t), (x)))))))
end
| FStar_SMTEncoding_Term.FreeV (uu____42) -> begin
(let _0_353 = (f FStar_SMTEncoding_Util.mkTrue)
in ((true), (_0_353), (negs), (t)))
end
| uu____45 -> begin
((false), (FStar_SMTEncoding_Util.mkFalse), (FStar_SMTEncoding_Util.mkFalse), (FStar_SMTEncoding_Util.mkFalse))
end)
end))


let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> (match ((n <= (Prims.parse_int "0"))) with
| true -> begin
(Prims.raise FStar_Util.Impos)
end
| uu____76 -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (uu____81) -> begin
(let _0_355 = (FStar_SMTEncoding_Util.mkAnd (let _0_354 = (FStar_SMTEncoding_Util.mkNot t)
in ((negs), (_0_354))))
in ((true), (l), (_0_355)))
end
| uu____85 -> begin
(

let uu____86 = (get_next_n_ite n t negs (fun x -> x))
in (match (uu____86) with
| (b, t, negs', rest) -> begin
(match (b) with
| true -> begin
(let _0_357 = (let _0_356 = (FStar_SMTEncoding_Util.mkImp ((negs), (t)))
in (_0_356)::l)
in (is_ite_all_the_way n rest negs' _0_357))
end
| uu____104 -> begin
((false), ([]), (FStar_SMTEncoding_Util.mkFalse))
end)
end))
end)
end))


let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (f (FStar_SMTEncoding_Util.mkForall'' ((l), (opt), (l'), (x))))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (t1)::(t2)::uu____163) -> begin
(

let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, uu____183, uu____184, uu____185, uu____186) -> begin
(parse_query_for_split_cases n t2 (fun x -> (f (FStar_SMTEncoding_Util.mkImp ((t1), (x))))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, uu____196) -> begin
(

let uu____199 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Util.mkTrue [])
in (match (uu____199) with
| (b, l, negs) -> begin
((b), ((((fun x -> (f (FStar_SMTEncoding_Util.mkImp ((t1), (x)))))), (l), (negs))))
end))
end
| uu____227 -> begin
((false), ((((fun uu____237 -> FStar_SMTEncoding_Util.mkFalse)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, uu____238) -> begin
(

let uu____241 = (is_ite_all_the_way n t FStar_SMTEncoding_Util.mkTrue [])
in (match (uu____241) with
| (b, l, negs) -> begin
((b), (((f), (l), (negs))))
end))
end
| uu____268 -> begin
((false), ((((fun uu____278 -> FStar_SMTEncoding_Util.mkFalse)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end))


let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, (hd)::uu____283) -> begin
hd
end
| uu____286 -> begin
t
end))


let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (check (FStar_SMTEncoding_Term.Assume ((let _0_358 = (FStar_SMTEncoding_Util.mkNot (f t))
in ((_0_358), (None), (None))))))) (FStar_List.rev l)))


let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (check (FStar_SMTEncoding_Term.Assume ((let _0_359 = (FStar_SMTEncoding_Util.mkNot (f (FStar_SMTEncoding_Util.mkNot negs)))
in ((_0_359), (None), (None)))))))


let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', uu____363, uu____364) -> begin
(let _0_360 = (strip_not q')
in (parse_query_for_split_cases n _0_360 (fun x -> x)))
end
| uu____368 -> begin
((false), ((((fun x -> x)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end))


let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun uu____393 check -> (match (uu____393) with
| (f, l, negs) -> begin
((check_split_cases f l check);
(check_exhaustiveness f negs check);
)
end))






open Prims
open FStar_Pervasives
type order =
| Lt
| Eq
| Gt


let uu___is_Lt : order  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Lt -> begin
true
end
| uu____5 -> begin
false
end))


let uu___is_Eq : order  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____10 -> begin
false
end))


let uu___is_Gt : order  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gt -> begin
true
end
| uu____15 -> begin
false
end))


let ge : order  ->  Prims.bool = (fun o -> (o <> Lt))


let le : order  ->  Prims.bool = (fun o -> (o <> Gt))


let ne : order  ->  Prims.bool = (fun o -> (o <> Eq))


let gt : order  ->  Prims.bool = (fun o -> (o = Gt))


let lt : order  ->  Prims.bool = (fun o -> (o = Lt))


let eq : order  ->  Prims.bool = (fun o -> (o = Eq))


let lex : order  ->  (Prims.unit  ->  order)  ->  order = (fun o1 o2 -> (match (((o1), (o2))) with
| (Lt, uu____55) -> begin
Lt
end
| (Eq, uu____60) -> begin
(o2 ())
end
| (Gt, uu____65) -> begin
Gt
end))


let order_from_int : Prims.int  ->  order = (fun i -> (match ((i < (Prims.parse_int "0"))) with
| true -> begin
Lt
end
| uu____74 -> begin
(match ((i = (Prims.parse_int "0"))) with
| true -> begin
Eq
end
| uu____75 -> begin
Gt
end)
end))


let compare_int : Prims.int  ->  Prims.int  ->  order = (fun i j -> (order_from_int (i - j)))


let rec compare_list : 'a . ('a  ->  'a  ->  order)  ->  'a Prims.list  ->  'a Prims.list  ->  order = (fun f l1 l2 -> (match (((l1), (l2))) with
| ([], []) -> begin
Eq
end
| ([], uu____131) -> begin
Lt
end
| (uu____138, []) -> begin
Gt
end
| ((x)::xs, (y)::ys) -> begin
(

let uu____157 = (f x y)
in (lex uu____157 (fun uu____159 -> (compare_list f xs ys))))
end))






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
| uu____8 -> begin
false
end))


let uu___is_Eq : order  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eq -> begin
true
end
| uu____19 -> begin
false
end))


let uu___is_Gt : order  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Gt -> begin
true
end
| uu____30 -> begin
false
end))


let ge : order  ->  Prims.bool = (fun o -> (Prims.op_disEquality o Lt))


let le : order  ->  Prims.bool = (fun o -> (Prims.op_disEquality o Gt))


let ne : order  ->  Prims.bool = (fun o -> (Prims.op_disEquality o Eq))


let gt : order  ->  Prims.bool = (fun o -> (Prims.op_Equality o Gt))


let lt : order  ->  Prims.bool = (fun o -> (Prims.op_Equality o Lt))


let eq : order  ->  Prims.bool = (fun o -> (Prims.op_Equality o Eq))


let lex : order  ->  (unit  ->  order)  ->  order = (fun o1 o2 -> (match (((o1), (o2))) with
| (Lt, uu____99) -> begin
Lt
end
| (Eq, uu____106) -> begin
(o2 ())
end
| (Gt, uu____113) -> begin
Gt
end))


let order_from_int : Prims.int  ->  order = (fun i -> (match ((i < (Prims.parse_int "0"))) with
| true -> begin
Lt
end
| uu____130 -> begin
(match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
Eq
end
| uu____135 -> begin
Gt
end)
end))


let compare_int : Prims.int  ->  Prims.int  ->  order = (fun i j -> (order_from_int (i - j)))


let rec compare_list : 'a . ('a  ->  'a  ->  order)  ->  'a Prims.list  ->  'a Prims.list  ->  order = (fun f l1 l2 -> (match (((l1), (l2))) with
| ([], []) -> begin
Eq
end
| ([], uu____204) -> begin
Lt
end
| (uu____211, []) -> begin
Gt
end
| ((x)::xs, (y)::ys) -> begin
(

let uu____230 = (f x y)
in (lex uu____230 (fun uu____232 -> (compare_list f xs ys))))
end))


let compare_option : 'a . ('a  ->  'a  ->  order)  ->  'a FStar_Pervasives_Native.option  ->  'a FStar_Pervasives_Native.option  ->  order = (fun f x y -> (match (((x), (y))) with
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> begin
Eq
end
| (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some (uu____284)) -> begin
Lt
end
| (FStar_Pervasives_Native.Some (uu____289), FStar_Pervasives_Native.None) -> begin
Gt
end
| (FStar_Pervasives_Native.Some (x1), FStar_Pervasives_Native.Some (y1)) -> begin
(f x1 y1)
end))





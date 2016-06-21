
open Prims

let n : Prims.int = (Prims.parse_int "63")

type t' =
| Mk of Prims.unit FStar_Int.int_t


let ___Mk___v : t'  ->  Prims.unit FStar_Int.int_t = (fun projectee -> (match ((Obj.magic (projectee))) with
| Mk (v) -> begin
v
end))


type t =
t'


let v : t  ->  Prims.unit FStar_Int.int_t = (fun x -> (___Mk___v x))


let add : t  ->  t  ->  t = (fun a b -> Mk ((FStar_Int.add n (v a) (v b))))


let add_underspec : t  ->  t  ->  t = (fun a b -> Mk ((FStar_Int.add_underspec n (v a) (v b))))


let add_mod : t  ->  t  ->  t = (fun a b -> Mk ((FStar_Int.add_mod n (v a) (v b))))


let sub : t  ->  t  ->  t = (fun a b -> Mk ((FStar_Int.sub n (v a) (v b))))


let sub_underspec : t  ->  t  ->  t = (fun a b -> Mk ((FStar_Int.sub_underspec n (v a) (v b))))


let sub_mod : t  ->  t  ->  t = (fun a b -> Mk ((FStar_Int.sub_mod n (v a) (v b))))


let mul : t  ->  t  ->  t = (fun a b -> Mk ((FStar_Int.mul n (v a) (v b))))


let mul_underspec : t  ->  t  ->  t = (fun a b -> Mk ((FStar_Int.mul_underspec n (v a) (v b))))


let mul_mod : t  ->  t  ->  t = (fun a b -> Mk ((FStar_Int.mul_mod n (v a) (v b))))


let div : t  ->  t  ->  t = (fun a b -> Mk ((FStar_Int.div n (v a) (v b))))


let div_underspec : t  ->  t  ->  t = (fun a b -> Mk ((FStar_Int.div_underspec n (v a) (v b))))


let mod : t  ->  t  ->  t = (fun a b -> Mk ((FStar_Int.mod n (v a) (v b))))


let logand : t  ->  t  ->  t = (fun a b -> Mk ((FStar_Int.logand n (v a) (v b))))


let logxor : t  ->  t  ->  t = (fun a b -> Mk ((FStar_Int.logxor n (v a) (v b))))


let logor : t  ->  t  ->  t = (fun a b -> Mk ((FStar_Int.logor n (v a) (v b))))


let lognot : t  ->  t = (fun a -> Mk ((FStar_Int.lognot n (v a))))


let int_to_t : Prims.unit FStar_Int.int_t  ->  t = (fun x -> Mk (x))


let shift_right : t  ->  FStar_UInt32.t  ->  t = (fun a s -> Mk ((FStar_Int.shift_right n (v a) (FStar_UInt32.v s))))


let shift_left : t  ->  FStar_UInt32.t  ->  t = (fun a s -> Mk ((FStar_Int.shift_left n (v a) (FStar_UInt32.v s))))


let eq : t  ->  t  ->  Prims.bool = (fun a b -> (FStar_Int.eq n (v a) (v b)))


let gt : t  ->  t  ->  Prims.bool = (fun a b -> (FStar_Int.gt n (v a) (v b)))


let gte : t  ->  t  ->  Prims.bool = (fun a b -> (FStar_Int.gte n (v a) (v b)))


let lt : t  ->  t  ->  Prims.bool = (fun a b -> (FStar_Int.lt n (v a) (v b)))


let lte : t  ->  t  ->  Prims.bool = (fun a b -> (FStar_Int.lte n (v a) (v b)))


let op_Plus_Hat : t  ->  t  ->  t = add


let op_Plus_Question_Hat : t  ->  t  ->  t = add_underspec


let op_Plus_Percent_Hat : t  ->  t  ->  t = add_mod


let op_Subtraction_Hat : t  ->  t  ->  t = sub


let op_Subtraction_Question_Hat : t  ->  t  ->  t = sub_underspec


let op_Subtraction_Percent_Hat : t  ->  t  ->  t = sub_mod


let op_Star_Hat : t  ->  t  ->  t = mul


let op_Star_Question_Hat : t  ->  t  ->  t = mul_underspec


let op_Star_Percent_Hat : t  ->  t  ->  t = mul_mod


let op_Slash_Hat : t  ->  t  ->  t = div


let op_Percent_Hat : t  ->  t  ->  t = mod


let op_Hat_Hat : t  ->  t  ->  t = logxor


let op_Amp_Hat : t  ->  t  ->  t = logand


let op_Bar_Hat : t  ->  t  ->  t = logor


let op_Less_Less_Hat : t  ->  FStar_UInt32.t  ->  t = shift_left


let op_Greater_Greater_Hat : t  ->  FStar_UInt32.t  ->  t = shift_right


let op_Equal_Hat : t  ->  t  ->  Prims.bool = eq


let op_Greater_Hat : t  ->  t  ->  Prims.bool = gt


let op_Greater_Equal_Hat : t  ->  t  ->  Prims.bool = gte


let op_Less_Hat : t  ->  t  ->  Prims.bool = gt


let op_Less_Equal_Hat : t  ->  t  ->  Prims.bool = gte





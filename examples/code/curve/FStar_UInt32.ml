
open Prims

let n : Prims.int = (Prims.parse_int "32")

type t' =
| Mk of Prims.unit FStar_UInt.uint_t


let ___Mk___v : t'  ->  Prims.unit FStar_UInt.uint_t = (fun projectee -> (match ((Obj.magic (projectee))) with
| Mk (v) -> begin
v
end))


type t =
t'


let v : t  ->  Prims.unit FStar_UInt.uint_t = (fun x -> (___Mk___v x))


let add : t  ->  t  ->  t = (fun a b -> Mk ((FStar_UInt.add n (v a) (v b))))


let add_underspec : t  ->  t  ->  t = (fun a b -> Mk ((FStar_UInt.add_underspec n (v a) (v b))))


let add_mod : t  ->  t  ->  t = (fun a b -> Mk ((FStar_UInt.add_mod n (v a) (v b))))


let sub : t  ->  t  ->  t = (fun a b -> Mk ((FStar_UInt.sub n (v a) (v b))))


let sub_underspec : t  ->  t  ->  t = (fun a b -> Mk ((FStar_UInt.sub_underspec n (v a) (v b))))


let sub_mod : t  ->  t  ->  t = (fun a b -> Mk ((FStar_UInt.sub_mod n (v a) (v b))))


let mul : t  ->  t  ->  t = (fun a b -> Mk ((FStar_UInt.mul n (v a) (v b))))


let mul_underspec : t  ->  t  ->  t = (fun a b -> Mk ((FStar_UInt.mul_underspec n (v a) (v b))))


let mul_mod : t  ->  t  ->  t = (fun a b -> Mk ((FStar_UInt.mul_mod n (v a) (v b))))


let div : t  ->  t  ->  t = (fun a b -> Mk ((FStar_UInt.div n (v a) (v b))))


let div_underspec : t  ->  t  ->  t = (fun a b -> Mk ((FStar_UInt.div_underspec n (v a) (v b))))


let rem : t  ->  t  ->  t = (fun a b -> Mk ((FStar_UInt.mod n (v a) (v b))))


let logand : t  ->  t  ->  t = (fun a b -> Mk ((FStar_UInt.logand n (v a) (v b))))


let logxor : t  ->  t  ->  t = (fun a b -> Mk ((FStar_UInt.logxor n (v a) (v b))))


let logor : t  ->  t  ->  t = (fun a b -> Mk ((FStar_UInt.logor n (v a) (v b))))


let lognot : t  ->  t = (fun a -> Mk ((FStar_UInt.lognot n (v a))))


let uint_to_t : Prims.unit FStar_UInt.uint_t  ->  t = (fun x -> Mk (x))


let shift_right : t  ->  t  ->  t = (fun a s -> Mk ((FStar_UInt.shift_right n (v a) (v s))))


let shift_left : t  ->  t  ->  t = (fun a s -> Mk ((FStar_UInt.shift_left n (v a) (v s))))


let eq : t  ->  t  ->  Prims.bool = (fun a b -> (FStar_UInt.eq n (v a) (v b)))


let gt : t  ->  t  ->  Prims.bool = (fun a b -> (FStar_UInt.gt n (v a) (v b)))


let gte : t  ->  t  ->  Prims.bool = (fun a b -> (FStar_UInt.gte n (v a) (v b)))


let lt : t  ->  t  ->  Prims.bool = (fun a b -> (FStar_UInt.lt n (v a) (v b)))


let lte : t  ->  t  ->  Prims.bool = (fun a b -> (FStar_UInt.lte n (v a) (v b)))


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


let op_Percent_Hat : t  ->  t  ->  t = rem


let op_Hat_Hat : t  ->  t  ->  t = logxor


let op_Amp_Hat : t  ->  t  ->  t = logand


let op_Bar_Hat : t  ->  t  ->  t = logor


let op_Less_Less_Hat : t  ->  t  ->  t = shift_left


let op_Greater_Greater_Hat : t  ->  t  ->  t = shift_right


let op_Equals_Hat : t  ->  t  ->  Prims.bool = eq


let op_Greater_Hat : t  ->  t  ->  Prims.bool = gt


let op_Greater_Equal_Hat : t  ->  t  ->  Prims.bool = gte


let op_Less_Hat : t  ->  t  ->  Prims.bool = gt


let op_Less_Equal_Hat : t  ->  t  ->  Prims.bool = gte


let to_int : t  ->  Prims.int = (fun x -> (v x))


let to_string : t  ->  Prims.string = (Obj.magic ((fun __1395 -> ())))


let of_string : Prims.string  ->  t = (Obj.magic ((fun __1399 -> ())))





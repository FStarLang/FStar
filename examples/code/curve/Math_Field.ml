
open Prims

type felem =
Prims.unit


let zero : felem = (Obj.magic (()))


type non_zero =
felem


let one : non_zero = (Obj.magic (()))


let add : felem  ->  felem  ->  felem = (Obj.magic ((fun __10 __11 -> ())))


let mul : felem  ->  felem  ->  felem = (Obj.magic ((fun __18 __19 -> ())))


let opp : felem  ->  felem = (Obj.magic ((fun x -> ())))


let inv : non_zero  ->  non_zero = (Obj.magic ((fun x -> ())))


let mul_non_zero : non_zero  ->  non_zero  ->  non_zero = (Obj.magic ((fun x y -> ())))


let field_is_group_1 : Prims.unit  ->  Prims.unit = (fun __54 -> ())


let field_is_group_2 : Prims.unit  ->  Prims.unit = (fun __58 -> ())


let field_is_commutative_field : Prims.unit  ->  Prims.unit = (fun __62 -> ())


type ('A__65, 'A__66) equal =
Prims.unit


let lemma_equal_intro : felem  ->  felem  ->  Prims.unit = (fun x y -> ())


let lemma_equal_elim : felem  ->  felem  ->  Prims.unit = (fun x y -> ())


let lemma_equal_refl : felem  ->  felem  ->  Prims.unit = (fun x y -> ())


let sub : felem  ->  felem  ->  felem = (fun x y -> (add x (opp y)))


let div : felem  ->  felem  ->  felem = (fun x y -> (mul x (inv y)))


let op_Hat_Plus : felem  ->  felem  ->  felem = add


let op_Hat_Star : felem  ->  felem  ->  felem = mul


let op_Plus_Star : Prims.nat  ->  felem  ->  felem = (fun n x -> (Math_Definitions.scalar_multiplication zero opp add n x))


let rec op_Hat_Hat : felem  ->  Prims.nat  ->  felem = (fun x n -> (match (n) with
| _0_21 when (_0_21 = (Prims.parse_int "0")) -> begin
one
end
| uu____138 -> begin
(mul x (op_Hat_Hat x (n - (Prims.parse_int "1"))))
end))


let op_Hat_Subtraction : felem  ->  felem  ->  felem = sub


let op_Hat_Slash : felem  ->  felem  ->  felem = div


let characteristic : Prims.nat = (Obj.magic (()))


let sub_lemma : felem  ->  felem  ->  Prims.unit = (fun x y -> ())


let to_felem : Prims.int  ->  felem = (Obj.magic ((fun x -> ())))





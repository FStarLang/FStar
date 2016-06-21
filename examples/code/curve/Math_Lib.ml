
open Prims

let rec pow2 : Prims.nat  ->  Prims.pos = (fun n -> (match ((n = (Prims.parse_int "0"))) with
| true -> begin
(Prims.parse_int "1")
end
| uu____10 -> begin
(FStar_Mul.op_Star (Prims.parse_int "2") (pow2 (n - (Prims.parse_int "1"))))
end))


let rec powx : Prims.int  ->  Prims.nat  ->  Prims.int = (fun x n -> (match (n) with
| _0_1 when (_0_1 = (Prims.parse_int "0")) -> begin
(Prims.parse_int "1")
end
| uu____25 -> begin
(FStar_Mul.op_Star x (powx x (n - (Prims.parse_int "1"))))
end))


let powx_lemma1 : Prims.int  ->  Prims.unit = (fun a -> ())


let rec powx_lemma2 : Prims.int  ->  Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun x n m -> ())


let abs : Prims.int  ->  Prims.int = (fun x -> (match ((x >= (Prims.parse_int "0"))) with
| true -> begin
x
end
| uu____57 -> begin
((Prims.parse_int "0") - x)
end))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun x y -> (match ((x >= y)) with
| true -> begin
x
end
| uu____66 -> begin
y
end))


let min : Prims.int  ->  Prims.int  ->  Prims.int = (fun x y -> (match ((x >= y)) with
| true -> begin
y
end
| uu____75 -> begin
x
end))


let div : Prims.int  ->  Prims.pos  ->  Prims.int = (fun a b -> (match ((a < (Prims.parse_int "0"))) with
| true -> begin
(match (((a % b) = (Prims.parse_int "0"))) with
| true -> begin
((Prims.parse_int "0") - ((Prims.parse_int "0") - (a / b)))
end
| uu____91 -> begin
(((Prims.parse_int "0") - ((Prims.parse_int "0") - (a / b))) - (Prims.parse_int "1"))
end)
end
| uu____94 -> begin
(a / b)
end))


let div_non_eucl : Prims.int  ->  Prims.pos  ->  Prims.int = (fun a b -> (match ((a < (Prims.parse_int "0"))) with
| true -> begin
((Prims.parse_int "0") - (((Prims.parse_int "0") - a) / b))
end
| uu____109 -> begin
(a / b)
end))


let shift_left : Prims.int  ->  Prims.nat  ->  Prims.int = (fun v i -> (FStar_Mul.op_Star v (pow2 i)))


let arithmetic_shift_right : Prims.int  ->  Prims.nat  ->  Prims.int = (fun v i -> (div v (pow2 i)))


let signed_modulo : Prims.int  ->  Prims.pos  ->  Prims.int = (fun v p -> (match ((v >= (Prims.parse_int "0"))) with
| true -> begin
(v % p)
end
| uu____152 -> begin
((Prims.parse_int "0") - (((Prims.parse_int "0") - v) % p))
end))


let op_Plus_Percent : Prims.int  ->  Prims.pos  ->  Prims.int = (fun a p -> (signed_modulo a p))


let xor_op : Prims.int  ->  Prims.int  ->  Prims.int = (Obj.magic ((fun x y -> ())))


let and_op : Prims.int  ->  Prims.int  ->  Prims.int = (Obj.magic ((fun x y -> ())))


let or_op : Prims.int  ->  Prims.int  ->  Prims.int = (Obj.magic ((fun x y -> ())))


let lnot_op : Prims.int  ->  Prims.int = (Obj.magic ((fun __196 -> ())))


let compare : Prims.int  ->  Prims.int  ->  Prims.int = (Obj.magic ((fun x y -> ())))


let rec pow2_increases_lemma : Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun n m -> ())


let rec pow2_exp_lemma : Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun n m -> ())


let pow2_div_lemma : Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun n m -> ())


let abs_mul_lemma : Prims.int  ->  Prims.int  ->  Prims.unit = (fun a b -> ())


let div_non_eucl_decr_lemma : Prims.int  ->  Prims.pos  ->  Prims.unit = (fun a b -> ())


let div_non_eucl_bigger_denom_lemma : Prims.int  ->  Prims.pos  ->  Prims.unit = (fun a b -> ())


let signed_modulo_property : Prims.int  ->  Prims.pos  ->  Prims.unit = (fun v p -> ())


let multiply_fractions_lemma : Prims.nat  ->  Prims.pos  ->  Prims.unit = (fun a n -> ())


let mul_pos_strict_incr_lemma : Prims.pos  ->  Prims.int  ->  Prims.pos  ->  Prims.unit = (fun a b c -> ())


let mul_incr_lemma : Prims.nat  ->  Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun a b c -> ())


let parenSub : Prims.int  ->  Prims.int  ->  Prims.int  ->  Prims.unit = (fun a b c -> ())


let rec log_2 : Prims.pos  ->  Prims.nat = (fun x -> (match ((x >= (Prims.parse_int "2"))) with
| true -> begin
((Prims.parse_int "1") + (log_2 (x / (Prims.parse_int "2"))))
end
| uu____412 -> begin
(Prims.parse_int "0")
end))





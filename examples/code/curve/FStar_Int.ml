
open Prims

let op_Slash : Prims.int  ->  Prims.int  ->  Prims.int = (fun a b -> (match ((((a >= (Prims.parse_int "0")) && (b < (Prims.parse_int "0"))) || ((a < (Prims.parse_int "0")) && (b >= (Prims.parse_int "0"))))) with
| true -> begin
(- (((Prims.abs a) / (Prims.abs b))))
end
| uu____10 -> begin
((Prims.abs a) / (Prims.abs b))
end))


let div_eucl : Prims.int  ->  Prims.nonzero  ->  Prims.int = (fun a b -> (match ((a < (Prims.parse_int "0"))) with
| true -> begin
(match (((a % b) = (Prims.parse_int "0"))) with
| true -> begin
(- ((op_Slash (- (a)) b)))
end
| uu____23 -> begin
((- ((op_Slash (- (a)) b))) - (Prims.parse_int "1"))
end)
end
| uu____26 -> begin
(op_Slash a b)
end))


let op_Slash_Percent : Prims.int  ->  Prims.nonzero  ->  Prims.int = div_eucl


let op_At_Percent : Prims.int  ->  Prims.int  ->  Prims.int = (fun v p -> (

let m = (v % p)
in (match ((m >= (op_Slash p (Prims.parse_int "2")))) with
| true -> begin
(m - p)
end
| uu____44 -> begin
m
end)))


let max_int : Prims.pos  ->  Prims.int = (fun n -> ((Prims.pow2 (n - (Prims.parse_int "1"))) - (Prims.parse_int "1")))


let min_int : Prims.pos  ->  Prims.int = (fun n -> (- ((Prims.pow2 (n - (Prims.parse_int "1"))))))


let fits : Prims.int  ->  Prims.pos  ->  Prims.bool = (fun x n -> (((min_int n) <= x) && (x <= (max_int n))))


type ('Ax, 'An) size =
Prims.unit Prims.b2t


type 'An int_t =
Prims.int


let add : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.unit int_t = (fun n a b -> (a + b))


let add_underspec : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.unit int_t = (fun n a b -> (match ((fits (a + b) n)) with
| true -> begin
(a + b)
end
| uu____381 -> begin
(Prims.magic ())
end))


let add_mod : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.unit int_t = (fun n a b -> (op_At_Percent (a + b) (Prims.pow2 n)))


let sub : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.unit int_t = (fun n a b -> (a - b))


let sub_underspec : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.unit int_t = (fun n a b -> (match ((fits (a - b) n)) with
| true -> begin
(a - b)
end
| uu____812 -> begin
(Prims.magic ())
end))


let sub_mod : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.unit int_t = (fun n a b -> (op_At_Percent (a - b) (Prims.pow2 n)))


let mul : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.unit int_t = (fun n a b -> (FStar_Mul.op_Star a b))


let mul_underspec : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.unit int_t = (fun n a b -> (match ((fits (FStar_Mul.op_Star a b) n)) with
| true -> begin
(FStar_Mul.op_Star a b)
end
| uu____1243 -> begin
(Prims.magic ())
end))


let mul_mod : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.unit int_t = (fun n a b -> (op_At_Percent (FStar_Mul.op_Star a b) (Prims.pow2 n)))


let div : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.unit int_t = (fun n a b -> (op_Slash a b))


let div_underspec : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.unit int_t = (fun n a b -> (match ((fits (op_Slash a b) n)) with
| true -> begin
(op_Slash a b)
end
| uu____1680 -> begin
(Prims.magic ())
end))


let mod : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.unit int_t = (fun n a b -> (a - (FStar_Mul.op_Star (op_Slash a b) b)))


let logand : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.unit int_t = (Obj.magic ((fun n __1915 __1916 -> ())))


let logxor : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.unit int_t = (Obj.magic ((fun n __1994 __1995 -> ())))


let logor : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.unit int_t = (Obj.magic ((fun n __2073 __2074 -> ())))


let lognot : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t = (Obj.magic ((fun n __2138 -> ())))


let eq : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.bool = (fun n a b -> (a = b))


let gt : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.bool = (fun n a b -> (a > b))


let gte : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.bool = (fun n a b -> (a >= b))


let lt : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.bool = (fun n a b -> (a < b))


let lte : Prims.pos  ->  Prims.unit int_t  ->  Prims.unit int_t  ->  Prims.bool = (fun n a b -> (a <= b))


let to_int_t : Prims.pos  ->  Prims.int  ->  Prims.unit int_t = (fun m a -> (op_At_Percent a (Prims.pow2 m)))


let shift_right : Prims.pos  ->  Prims.unit int_t  ->  Prims.nat  ->  Prims.unit int_t = (Obj.magic ((fun n a s -> ())))


let shift_left : Prims.pos  ->  Prims.unit int_t  ->  Prims.nat  ->  Prims.unit int_t = (fun n a s -> (op_At_Percent (FStar_Mul.op_Star a (Prims.pow2 s)) (Prims.pow2 n)))





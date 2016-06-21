
open Prims

let max_int : Prims.pos  ->  Prims.int = (fun n -> ((Prims.pow2 n) - (Prims.parse_int "1")))


let min_int : Prims.pos  ->  Prims.int = (fun n -> (Prims.parse_int "0"))


let fits : Prims.int  ->  Prims.pos  ->  Prims.bool = (fun x n -> (((min_int n) <= x) && (x <= (max_int n))))


type ('Ax, 'An) size =
Prims.unit Prims.b2t


type 'An uint_t =
Prims.int


let zero : Prims.pos  ->  Prims.unit uint_t = (fun n -> (Prims.parse_int "0"))


let one : Prims.pos  ->  Prims.unit uint_t = (fun n -> (Prims.parse_int "1"))


let ones : Prims.pos  ->  Prims.unit uint_t = (fun n -> (max_int n))


let incr : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a -> (a + (Prims.parse_int "1")))


let decr : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a -> (a - (Prims.parse_int "1")))


let incr_underspec : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a -> (match ((a < (max_int n))) with
| true -> begin
(a + (Prims.parse_int "1"))
end
| uu____304 -> begin
(Prims.magic ())
end))


let decr_underspec : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a -> (match ((a > (min_int n))) with
| true -> begin
(a - (Prims.parse_int "1"))
end
| uu____398 -> begin
(Prims.magic ())
end))


let incr_mod : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a -> ((a + (Prims.parse_int "1")) % (Prims.pow2 n)))


let decr_mod : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a -> ((a - (Prims.parse_int "1")) % (Prims.pow2 n)))


let add : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a b -> (a + b))


let add_underspec : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a b -> (match ((fits (a + b) n)) with
| true -> begin
(a + b)
end
| uu____743 -> begin
(Prims.magic ())
end))


let add_mod : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a b -> ((a + b) % (Prims.pow2 n)))


let sub : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a b -> (a - b))


let sub_underspec : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a b -> (match ((fits (a - b) n)) with
| true -> begin
(a - b)
end
| uu____1057 -> begin
(Prims.magic ())
end))


let sub_mod : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a b -> ((a - b) % (Prims.pow2 n)))


let mul : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a b -> (FStar_Mul.op_Star a b))


let mul_underspec : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a b -> (match ((fits (FStar_Mul.op_Star a b) n)) with
| true -> begin
(FStar_Mul.op_Star a b)
end
| uu____1371 -> begin
(Prims.magic ())
end))


let mul_mod : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a b -> ((FStar_Mul.op_Star a b) % (Prims.pow2 n)))


let div : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a b -> (a / b))


let div_underspec : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a b -> (match ((fits (a / b) n)) with
| true -> begin
(a / b)
end
| uu____1691 -> begin
(Prims.magic ())
end))


let mod : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (fun n a b -> (a - (FStar_Mul.op_Star (a / b) b)))


let logand : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (Obj.magic ((fun n __1863 __1864 -> ())))


let logxor : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (Obj.magic ((fun n __1924 __1925 -> ())))


let logor : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (Obj.magic ((fun n __1985 __1986 -> ())))


let lognot : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t = (Obj.magic ((fun n __2035 -> ())))


let eq : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.bool = (fun n a b -> (a = b))


let gt : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.bool = (fun n a b -> (a > b))


let gte : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.bool = (fun n a b -> (a >= b))


let lt : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.bool = (fun n a b -> (a < b))


let lte : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.bool = (fun n a b -> (a <= b))


let logand_lemma_1 : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit = (fun n a b -> ())


let logand_lemma_2 : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit = (fun n a -> ())


let logand_lemma_3 : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit = (fun n a -> ())


let logand_lemma_4 : Prims.pos  ->  Prims.unit uint_t  ->  Prims.nat  ->  Prims.unit uint_t  ->  Prims.unit = (fun n a m b -> ())


let logxor_lemma_1 : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit = (fun n a b -> ())


let logxor_lemma_2 : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit = (fun n a -> ())


let logxor_lemma_3 : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit = (fun n a -> ())


let logxor_lemma_4 : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit = (fun n a -> ())


let logor_lemma_1 : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit uint_t  ->  Prims.unit = (fun n a b -> ())


let logor_lemma_2 : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit = (fun n a -> ())


let logor_lemma_3 : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit = (fun n a -> ())


let lognot_lemma_1 : Prims.pos  ->  Prims.unit uint_t  ->  Prims.unit = (fun n a -> ())


let lognot_lemma_2 : Prims.pos  ->  Prims.unit = (fun n -> ())


let to_uint_t : Prims.pos  ->  Prims.int  ->  Prims.unit uint_t = (fun m a -> (a % (Prims.pow2 m)))


let shift_right : Prims.pos  ->  Prims.unit uint_t  ->  Prims.nat  ->  Prims.unit uint_t = (Obj.magic ((fun n a s -> ())))


let shift_left : Prims.pos  ->  Prims.unit uint_t  ->  Prims.nat  ->  Prims.unit uint_t = (fun n a s -> ((FStar_Mul.op_Star a (Prims.pow2 s)) % (Prims.pow2 n)))





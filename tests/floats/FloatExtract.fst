module FloatExtract

(* Test that FStar.Float32 and FStar.Float64 extract to C, mapping to the
   native C [float] and [double] types and their arithmetic/comparison
   operators. The golden output is FloatExtract.c.expected / .h.expected. *)

module F32 = FStar.Float32
module F64 = FStar.Float64

(* Float64 -> double *)

let f64_add (x y: F64.t) : F64.t = F64.add x y
let f64_sub (x y: F64.t) : F64.t = F64.sub x y
let f64_mul (x y: F64.t) : F64.t = F64.mul x y
let f64_div (x y: F64.t) : F64.t = F64.div x y
let f64_neg (x : F64.t) : F64.t = F64.zero `F64.sub` x
let f64_rcp (x : F64.t) : F64.t = F64.one `F64.div` x

let f64_lt  (x y: F64.t) : bool = F64.lt x y
let f64_lte (x y: F64.t) : bool = F64.lte x y
let f64_eq  (x y: F64.t) : bool = F64.ieee_eq x y

let f64_of_int (n: Int64.t) : F64.t = F64.of_int n
let f64_pi () : F64.t = F64.of_literal "3.141592653589793"

(* A compound expression: (x + y) * 2.0 *)
let f64_poly (x y: F64.t) : F64.t = F64.mul (F64.add x y) (F64.of_literal "2.0")

(* Float32 -> float *)

let f32_add (x y: F32.t) : F32.t = F32.add x y
let f32_sub (x y: F32.t) : F32.t = F32.sub x y
let f32_mul (x y: F32.t) : F32.t = F32.mul x y
let f32_div (x y: F32.t) : F32.t = F32.div x y
let f32_neg (x : F32.t) : F32.t = F32.zero `F32.sub` x
let f32_rcp (x : F32.t) : F32.t = F32.one `F32.div` x

let f32_lt  (x y: F32.t) : bool = F32.lt x y
let f32_lte (x y: F32.t) : bool = F32.lte x y
let f32_eq  (x y: F32.t) : bool = F32.ieee_eq x y

let f32_of_int (n: Int64.t) : F32.t = F32.of_int n
let f32_pi () : F32.t = F32.of_literal "3.141592653589793"

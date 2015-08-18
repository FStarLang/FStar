
let rec pow2 = (fun ( n ) -> if (n = 0) then begin
1
end else begin
(2 * (pow2 (n - 1)))
end)

let abs = (fun ( x ) -> if (x >= 0) then begin
x
end else begin
(- (x))
end)

let max = (fun ( x ) ( y ) -> if (x >= y) then begin
x
end else begin
y
end)

let min = (fun ( x ) ( y ) -> if (x >= y) then begin
y
end else begin
x
end)

let div = (fun ( a ) ( b ) -> if (a < 0) then begin
if ((a mod b) = 0) then begin
(- (((- (a)) / b)))
end else begin
((- (((- (a)) / b))) - 1)
end
end else begin
(a / b)
end)

let div_non_eucl = (fun ( a ) ( b ) -> if (a < 0) then begin
(- (((- (a)) / b)))
end else begin
(a / b)
end)

let shift_left = (fun ( v ) ( i ) -> (v * (pow2 i)))

let arithmetic_shift_right = (fun ( v ) ( i ) -> (div v (pow2 i)))

let signed_modulo = (fun ( v ) ( p ) -> if (v >= 0) then begin
(v mod p)
end else begin
(- (((- (v)) mod p)))
end)

let compare = (fun ( x ) ( y ) -> if (x = y) then begin
0
end else begin
if (x < y) then begin
(- (1))
end else begin
1
end
end)

let rec pow2_increases_lemma = (fun ( n ) ( m ) -> (match ((n - m)) with
| 1 -> begin
()
end
| _ -> begin
(let _10_62 = (pow2_increases_lemma (n - 1) m)
in (pow2_increases_lemma n (n - 1)))
end))

let rec pow2_exp_lemma = (fun ( n ) ( m ) -> (match (n) with
| 0 -> begin
()
end
| _ -> begin
(pow2_exp_lemma (n - 1) m)
end))

let pow2_div_lemma = (fun ( n ) ( m ) -> ())

let abs_mul_lemma = (fun ( a ) ( b ) -> ())

let div_non_eucl_decr_lemma = (fun ( a ) ( b ) -> ())

let div_non_eucl_bigger_denom_lemma = (fun ( a ) ( b ) -> ())

let signed_modulo_property = (fun ( v ) ( p ) -> ())

let multiply_fractions_lemma = (fun ( a ) ( n ) -> ())

let mul_pos_strict_incr_lemma = (fun ( a ) ( b ) ( c ) -> ())

let mul_incr_lemma = (fun ( a ) ( b ) ( c ) -> ())

let parenSub = (fun ( a ) ( b ) ( c ) -> ())

let log = (fun ( x ) -> (x - 1))

let log_incr_lemma = (fun ( a ) ( b ) -> ())

let log_lemma = (fun ( a ) ( b ) -> ())

let and_op a b = a land b
let or_op a b = a lor b
let xor_op a b = b lxor b
let not_op a = lnot a




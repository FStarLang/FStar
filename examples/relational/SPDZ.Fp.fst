module SPDZ.Fp
open FStar.Relational

(* TODO, actually turn this into Fp
   For now we just use ints because they have better automatic support... *)
assume type prime (p:pos)
type prime_number = p:pos{prime p}
assume val p:prime_number

(* type fp = i:int{0 <= i /\ i < p} *)
type fp = int

val mod_p : int -> Tot fp
let mod_p x = x //% p

val add_fp : fp -> fp -> Tot fp
let add_fp x y = mod_p (x + y)

val mul_fp : fp -> fp -> Tot fp
let mul_fp x y = mod_p (x * y)

val minus_fp : fp -> fp -> Tot fp
let minus_fp x y = add_fp x (mod_p (-y))

assume val div_fp : a:fp -> b:fp -> Tot (r:fp{mul_fp b r = a})

(*
let mod_laws1 = assume(forall a b.((a % p) + b) % p = (a + b) %p)
let mod_laws2 = assume(forall a b.(a + (b % p)) % p = (a + b) %p)
let mod_laws3 = assume(forall a b.((a % p) * b) % p = (a * b) %p)
let mod_laws4 = assume(forall a b.(a * (b % p)) % p = (a * b) %p)
let mod_laws5 = assume(forall a b.((a % p) - b) % p = (a - b) %p)
let mod_laws6 = assume(forall a b.(a - (b % p)) % p = (a - b) %p)
*)


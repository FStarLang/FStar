open Prims
let rec egcd (a : Prims.int) (b : Prims.int) (u1 : Prims.int)
  (u2 : Prims.int) (u3 : Prims.int) (v1 : Prims.int) (v2 : Prims.int)
  (v3 : Prims.int) : (Prims.int * Prims.int * Prims.int)=
  if v3 = Prims.int_zero
  then (u1, u2, u3)
  else
    (let q = u3 / v3 in
     let uu___ = (v1, (u1 - (q * v1))) in
     match uu___ with
     | (u11, v11) ->
         let uu___1 = (v2, (u2 - (q * v2))) in
         (match uu___1 with
          | (u21, v21) ->
              let u3' = u3 in
              let v3' = v3 in
              let uu___2 = (v3, (u3 - (q * v3))) in
              (match uu___2 with
               | (u31, v31) -> let r = egcd a b u11 u21 u31 v11 v21 v31 in r)))
let euclid_gcd (a : Prims.int) (b : Prims.int) :
  (Prims.int * Prims.int * Prims.int)=
  if b >= Prims.int_zero
  then egcd a b Prims.int_one Prims.int_zero a Prims.int_zero Prims.int_one b
  else
    (let res =
       egcd a b Prims.int_one Prims.int_zero a Prims.int_zero
         (Prims.of_int (-1)) (- b) in
     let uu___ = res in match uu___ with | (uu___1, uu___2, d) -> res)
let bezout_prime (p : Prims.int) (a : Prims.pos) : (Prims.int * Prims.int)=
  let uu___ = euclid_gcd p a in
  match uu___ with
  | (r, s, d) -> if d = Prims.int_one then (r, s) else ((- r), (- s))

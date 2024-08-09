open Prims
type ('a, 'b) divides = unit
type ('a, 'b, 'd) is_gcd = unit
let rec (egcd :
  Prims.int ->
    Prims.int ->
      Prims.int ->
        Prims.int ->
          Prims.int ->
            Prims.int ->
              Prims.int -> Prims.int -> (Prims.int * Prims.int * Prims.int))
  =
  fun a ->
    fun b ->
      fun u1 ->
        fun u2 ->
          fun u3 ->
            fun v1 ->
              fun v2 ->
                fun v3 ->
                  if v3 = Prims.int_zero
                  then (u1, u2, u3)
                  else
                    (let q = u3 / v3 in
                     let uu___1 = (v1, (u1 - (q * v1))) in
                     match uu___1 with
                     | (u11, v11) ->
                         let uu___2 = (v2, (u2 - (q * v2))) in
                         (match uu___2 with
                          | (u21, v21) ->
                              let u3' = u3 in
                              let v3' = v3 in
                              let uu___3 = (v3, (u3 - (q * v3))) in
                              (match uu___3 with
                               | (u31, v31) ->
                                   let r = egcd a b u11 u21 u31 v11 v21 v31 in
                                   r)))
let (euclid_gcd :
  Prims.int -> Prims.int -> (Prims.int * Prims.int * Prims.int)) =
  fun a ->
    fun b ->
      if b >= Prims.int_zero
      then
        egcd a b Prims.int_one Prims.int_zero a Prims.int_zero Prims.int_one
          b
      else
        (let res =
           egcd a b Prims.int_one Prims.int_zero a Prims.int_zero
             (Prims.of_int (-1)) (- b) in
         let uu___1 = res in match uu___1 with | (uu___2, uu___3, d) -> res)
type 'p is_prime = unit
let (bezout_prime : Prims.int -> Prims.pos -> (Prims.int * Prims.int)) =
  fun p ->
    fun a ->
      let uu___ = euclid_gcd p a in
      match uu___ with
      | (r, s, d) -> if d = Prims.int_one then (r, s) else ((- r), (- s))
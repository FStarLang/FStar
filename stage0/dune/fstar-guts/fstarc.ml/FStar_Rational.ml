open Prims
let pmul (a : Prims.pos) (b : Prims.pos) : Prims.pos= a * b
type frac = {
  n: Prims.int ;
  d: Prims.pos }
let __proj__Mkfrac__item__n (projectee : frac) : Prims.int=
  match projectee with | { n; d;_} -> n
let __proj__Mkfrac__item__d (projectee : frac) : Prims.pos=
  match projectee with | { n; d;_} -> d
type rat = frac
let num (q : rat) : Prims.int= q.n
let den (q : rat) : Prims.pos= q.d
let mk (n : Prims.int) (d : Prims.pos) : rat=
  let g = FStar_Rational_Gcd.gcd n d in { n = (n / g); d = (d / g) }
let of_int (n : Prims.int) : rat= mk n Prims.int_one
let zero : rat= of_int Prims.int_zero
let one : rat= of_int Prims.int_one
let two : rat= of_int (Prims.of_int 2)
let add (p : rat) (q : rat) : rat=
  mk (((num p) * (den q)) + ((num q) * (den p))) (pmul (den p) (den q))
let neg (p : rat) : rat= mk (- (num p)) (den p)
let mul (p : rat) (q : rat) : rat=
  mk ((num p) * (num q)) (pmul (den p) (den q))
let inv (p : rat) : rat=
  if (num p) = Prims.int_zero
  then zero
  else
    if (num p) > Prims.int_zero
    then mk (den p) (num p)
    else mk (- (den p)) (- (num p))
let sub (p : rat) (q : rat) : rat= add p (neg q)
let div (p : rat) (q : rat) : rat= mul p (inv q)
let lt (p : rat) (q : rat) : Prims.bool=
  ((num p) * (den q)) < ((num q) * (den p))
let le (p : rat) (q : rat) : Prims.bool= (lt p q) || (p = q)
let gt (p : rat) (q : rat) : Prims.bool= lt q p
let ge (p : rat) (q : rat) : Prims.bool= le q p
let floor (q : rat) : Prims.int= (num q) / (den q)
let mid (p : rat) (q : rat) : rat=
  mk (((num p) * (den q)) + ((num q) * (den p)))
    (pmul (pmul (den p) (den q)) (Prims.of_int 2))
let below (q : rat) : rat= let a = num q in let b = den q in mk (a - b) b
let above (q : rat) : rat= let a = num q in let b = den q in mk (a + b) b

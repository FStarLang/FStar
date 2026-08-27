open Prims
type real_literal_repr = {
  mantissa: Prims.int ;
  exponent: Prims.int }[@@deriving yojson,show]
let __proj__Mkreal_literal_repr__item__mantissa
  (projectee : real_literal_repr) : Prims.int=
  match projectee with | { mantissa; exponent;_} -> mantissa
let __proj__Mkreal_literal_repr__item__exponent
  (projectee : real_literal_repr) : Prims.int=
  match projectee with | { mantissa; exponent;_} -> exponent
let canonical (r : real_literal_repr) : Prims.bool=
  (r.exponent = Prims.int_zero) ||
    ((r.exponent < Prims.int_zero) &&
       (((mod) r.mantissa (Prims.of_int 10)) <> Prims.int_zero))
type real_literal = real_literal_repr[@@deriving yojson,show]
let rec pow10 (n : Prims.nat) : Prims.pos=
  if n = Prims.int_zero
  then Prims.int_one
  else (Prims.of_int 10) * (pow10 (n - Prims.int_one))
let rec strip (m : Prims.int) (e : Prims.int) : real_literal=
  if (e = Prims.int_zero) || (((mod) m (Prims.of_int 10)) <> Prims.int_zero)
  then { mantissa = m; exponent = e }
  else strip (m / (Prims.of_int 10)) (e + Prims.int_one)
let mk (m : Prims.int) (e : Prims.int) : real_literal=
  if e >= Prims.int_zero
  then { mantissa = (m * (pow10 e)); exponent = Prims.int_zero }
  else strip m e
let of_int (i : Prims.int) : real_literal=
  { mantissa = i; exponent = Prims.int_zero }
let rec ndigits (x : Prims.nat) : Prims.nat=
  if x < (Prims.of_int 10)
  then Prims.int_one
  else Prims.int_one + (ndigits (x / (Prims.of_int 10)))
let rec zeros (n : Prims.nat) (s : Prims.string) : Prims.string=
  if n = Prims.int_zero
  then s
  else zeros (n - Prims.int_one) (Prims.strcat "0" s)
let to_string (r : real_literal) : Prims.string=
  let m = if r.mantissa < Prims.int_zero then - (r.mantissa) else r.mantissa in
  let k = - (r.exponent) in
  let p = pow10 k in
  let fpart = (mod) m p in
  let pad =
    if (ndigits fpart) >= k then Prims.int_zero else k - (ndigits fpart) in
  Prims.strcat (if r.mantissa < Prims.int_zero then "-" else "")
    (Prims.strcat (Prims.string_of_int (m / p))
       (Prims.strcat "."
          (if k = Prims.int_zero
           then "0"
           else zeros pad (Prims.string_of_int fpart))))
let compare (r1 : real_literal) (r2 : real_literal) : Prims.int=
  let e = if r1.exponent <= r2.exponent then r1.exponent else r2.exponent in
  let m1 = r1.mantissa * (pow10 (r1.exponent - e)) in
  let m2 = r2.mantissa * (pow10 (r2.exponent - e)) in
  if m1 < m2
  then Prims.of_int (-1)
  else if m1 = m2 then Prims.int_zero else Prims.int_one

open Prims
type real = FStar_RealLiteral.real_literal[@@deriving yojson,show]
let mantissa (r : real) : Prims.int= r.FStar_RealLiteral.mantissa
let exponent (r : real) : Prims.int= r.FStar_RealLiteral.exponent
let mk : Prims.int -> Prims.int -> real= FStar_RealLiteral.mk
let try_mk (m : Prims.int) (e : Prims.int) :
  real FStar_Pervasives_Native.option=
  let r = mk m e in
  if ((mantissa r) = m) && ((exponent r) = e)
  then FStar_Pervasives_Native.Some r
  else FStar_Pervasives_Native.None
let of_int : Prims.int -> real= FStar_RealLiteral.of_int
let of_string : Prims.string -> real FStar_Pervasives_Native.option=
  FStar_RealLiteral_Parse.of_string
let to_string : real -> Prims.string= FStar_RealLiteral.to_string
let to_smt_string (r : real) : Prims.string=
  if (mantissa r) < Prims.int_zero
  then
    Prims.strcat "(- "
      (Prims.strcat (to_string (mk (- (mantissa r)) (exponent r))) ")")
  else to_string r
let cmp (r1 : real) (r2 : real) : FStarC_Order.order=
  FStarC_Order.compare_int (FStar_RealLiteral.compare r1 r2) Prims.int_zero

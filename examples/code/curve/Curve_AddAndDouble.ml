
open Prims

let w : FStar_Buffer.u32  ->  Prims.int = FStar_UInt32.v


let vv : Curve_Bigint.u128  ->  Prims.int = FStar_UInt128.v


let op_Plus_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.add


let op_Subtraction_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.sub


type heap =
FStar_HyperStack.mem


let op_Plus_Plus_Plus = (fun a b -> (FStar_Set.union a b))


let equation_1 : Math_Field.felem  ->  Math_Field.felem  ->  Math_Field.felem = (fun x2 z2 -> (Obj.magic (())))


let equation_2 : Math_Field.felem  ->  Math_Field.felem  ->  Math_Field.felem = (fun x2 z2 -> (Obj.magic (())))


let equation_3 : Math_Field.felem  ->  Math_Field.felem  ->  Math_Field.felem  ->  Math_Field.felem  ->  Math_Field.felem = (fun x2 z2 x3 z3 -> (Obj.magic (())))


let equation_4 : Math_Field.felem  ->  Math_Field.felem  ->  Math_Field.felem  ->  Math_Field.felem  ->  Math_Field.felem  ->  Math_Field.felem = (fun x2 z2 x3 z3 x1 -> (Obj.magic (())))


let double_and_add' : Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Prims.unit = (fun two_p two_p_plus_q p p_plus_q q -> (

let h0 = (FStar_HST.get ())
in (

let qmqp = (Curve_Point.get_x q)
in (

let x = (Curve_Point.get_x p)
in (

let z = (Curve_Point.get_z p)
in (

let xprime = (Curve_Point.get_x p_plus_q)
in (

let zprime = (Curve_Point.get_z p_plus_q)
in (

let x2 = (Curve_Point.get_x two_p)
in (

let z2 = (Curve_Point.get_z two_p)
in (

let origx = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (

let origxprime = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (

let zzz = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) (op_Subtraction_Bar (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.parse_int "2")) Curve_Parameters.nlength) (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (

let xx = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) (op_Subtraction_Bar (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.parse_int "2")) Curve_Parameters.nlength) (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (

let zz = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) (op_Subtraction_Bar (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.parse_int "2")) Curve_Parameters.nlength) (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (

let xxprime = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) (op_Subtraction_Bar (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.parse_int "2")) Curve_Parameters.nlength) (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (

let zzprime = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) (op_Subtraction_Bar (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.parse_int "2")) Curve_Parameters.nlength) (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (

let xxxprime = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) (op_Subtraction_Bar (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.parse_int "2")) Curve_Parameters.nlength) (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (

let zzzprime = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) (op_Subtraction_Bar (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.parse_int "2")) Curve_Parameters.nlength) (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (FStar_Buffer.blit x (FStar_UInt32.uint_to_t (Prims.parse_int "0")) origx (FStar_UInt32.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength);
(Curve_Bignum.fsum x z);
(Curve_Bignum.fdifference z origx);
(FStar_Buffer.blit xprime (FStar_UInt32.uint_to_t (Prims.parse_int "0")) origxprime (FStar_UInt32.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength);
(Curve_Bignum.fsum xprime zprime);
(Curve_Bignum.fdifference zprime origxprime);
(Curve_Bignum.fmul xxprime xprime z);
(Curve_Bignum.fmul zzprime x zprime);
(FStar_Buffer.blit xxprime (FStar_UInt32.uint_to_t (Prims.parse_int "0")) origxprime (FStar_UInt32.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength);
(Curve_Bignum.fsum xxprime zzprime);
(Curve_Bignum.fdifference zzprime origxprime);
(Curve_Bignum.fsquare xxxprime xxprime);
(Curve_Bignum.fsquare zzzprime zzprime);
(Curve_Bignum.fmul zzprime zzzprime qmqp);
(FStar_Buffer.blit xxxprime (FStar_UInt32.uint_to_t (Prims.parse_int "0")) (Curve_Point.get_x two_p_plus_q) (FStar_UInt32.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength);
(FStar_Buffer.blit zzprime (FStar_UInt32.uint_to_t (Prims.parse_int "0")) (Curve_Point.get_z two_p_plus_q) (FStar_UInt32.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength);
(Curve_Bignum.fsquare xx x);
(Curve_Bignum.fsquare zz z);
(Curve_Bignum.fmul x2 xx zz);
(Curve_Bignum.fdifference zz xx);
(Curve_Bignum.erase zzz Curve_Parameters.nlength (op_Subtraction_Bar Curve_Parameters.nlength (FStar_UInt32.uint_to_t (Prims.parse_int "1"))) (FStar_UInt32.uint_to_t (Prims.parse_int "0")));
(Curve_Bignum.fscalar zzz zz Curve_Parameters.a24);
(Curve_Bignum.fsum zzz xx);
(Curve_Bignum.fmul z2 zz zzz);
))))))))))))))))))


let double_and_add : Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Prims.unit = (fun two_p two_p_plus_q p p_plus_q q -> (double_and_add' two_p two_p_plus_q p p_plus_q q))





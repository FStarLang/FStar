
open Prims

let rec loop : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Prims.unit = (fun tmp v ctr -> (match (ctr) with
| _0_32 when (_0_32 = (Prims.parse_int "0")) -> begin
()
end
| uu____72 -> begin
(Curve_Bignum.fsquare tmp v);
(Curve_Bignum.fsquare v tmp);
(loop tmp v (ctr - (Prims.parse_int "1")));

end))


let crecip' : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun output z -> (

let z2 = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (

let z9 = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (

let z11 = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (

let z2_5_0 = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (

let z2_10_0 = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (

let z2_20_0 = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (

let z2_50_0 = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (

let z2_100_0 = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (

let t0 = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (

let t1 = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (Curve_Bignum.fsquare z2 z);
(Curve_Bignum.fsquare t1 z2);
(Curve_Bignum.fsquare t0 t1);
(Curve_Bignum.fmul z9 t0 z);
(Curve_Bignum.fmul z11 z9 z2);
(Curve_Bignum.fsquare t0 z11);
(Curve_Bignum.fmul z2_5_0 t0 z9);
(Curve_Bignum.fsquare t0 z2_5_0);
(Curve_Bignum.fsquare t1 t0);
(Curve_Bignum.fsquare t0 t1);
(Curve_Bignum.fsquare t1 t0);
(Curve_Bignum.fsquare t0 t1);
(Curve_Bignum.fmul z2_10_0 t0 z2_5_0);
(Curve_Bignum.fsquare t0 z2_10_0);
(Curve_Bignum.fsquare t1 t0);
(loop t0 t1 (Prims.parse_int "4"));
(Curve_Bignum.fmul z2_20_0 t1 z2_10_0);
(Curve_Bignum.fsquare t0 z2_20_0);
(Curve_Bignum.fsquare t1 t0);
(loop t0 t1 (Prims.parse_int "9"));
(Curve_Bignum.fmul t0 t1 z2_20_0);
(Curve_Bignum.fsquare t1 t0);
(Curve_Bignum.fsquare t0 t1);
(loop t1 t0 (Prims.parse_int "4"));
(Curve_Bignum.fmul z2_50_0 t0 z2_10_0);
(Curve_Bignum.fsquare t0 z2_50_0);
(Curve_Bignum.fsquare t1 t0);
(loop t0 t1 (Prims.parse_int "24"));
(Curve_Bignum.fmul z2_100_0 t1 z2_50_0);
(Curve_Bignum.fsquare t1 z2_100_0);
(Curve_Bignum.fsquare t0 t1);
(loop t1 t0 (Prims.parse_int "49"));
(Curve_Bignum.fmul t1 t0 z2_100_0);
(Curve_Bignum.fsquare t0 t1);
(Curve_Bignum.fsquare t1 t0);
(loop t0 t1 (Prims.parse_int "24"));
(Curve_Bignum.fmul t0 t1 z2_50_0);
(Curve_Bignum.fsquare t1 t0);
(Curve_Bignum.fsquare t0 t1);
(Curve_Bignum.fsquare t1 t0);
(Curve_Bignum.fsquare t0 t1);
(Curve_Bignum.fsquare t1 t0);
(Curve_Bignum.fmul output t1 z11);
)))))))))))






open Prims

let op_Plus_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.add


let op_Subtraction_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.sub


let helper_lemma_1 : Prims.nat  ->  Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun i len v -> ())


let fdifference_aux_1 : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  FStar_Buffer.u32  ->  Prims.unit = (fun a b ctr -> (

let h0 = (FStar_HST.get ())
in (

let i = ctr
in (

let ai = (FStar_Buffer.index a i)
in (

let bi = (FStar_Buffer.index b i)
in (

let z = (FStar_UInt64.op_Subtraction_Hat bi ai)
in (FStar_Buffer.upd a i z);
(

let h1 = (FStar_HST.get ())
in ());
))))))


let fdifference_aux_2_0 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Prims.unit = (fun h0 h1 h2 a b ctr -> ())


let fdifference_aux_2_1 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Prims.unit = (fun h0 h1 h2 a b ctr -> ())


let fdifference_aux_2 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Prims.unit = (fun h0 h1 h2 a b ctr -> ())


let rec fdifference_aux : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  FStar_Buffer.u32  ->  Prims.unit = (fun a b ctr -> (

let h0 = (FStar_HST.get ())
in (match ((FStar_UInt32.eq ctr Curve_Parameters.nlength)) with
| true -> begin
()
end
| uu____1270 -> begin
(fdifference_aux_1 a b ctr);
(

let h1 = (FStar_HST.get ())
in (fdifference_aux a b (op_Plus_Bar ctr (FStar_UInt32.uint_to_t (Prims.parse_int "1"))));
(

let h2 = (FStar_HST.get ())
in ());
);

end)))


let subtraction_lemma_aux : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.pos  ->  Prims.unit = (fun h0 h1 a b len -> ())


let rec subtraction_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Prims.unit = (fun h0 h1 a b len -> ())


let subtraction_max_value_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun h0 h1 a b c -> ())


let max_value_lemma : Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Prims.unit = (fun h a m -> ())


let subtraction_max_value_lemma_extended : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun h0 h1 a b c -> ())


let auxiliary_lemma_2 : Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Prims.unit = (fun ha a hb b i -> ())


let auxiliary_lemma_0 : Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun ha a hb b -> ())


let fdifference' : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun a b -> (

let h0 = (FStar_HST.get ())
in (fdifference_aux a b (FStar_UInt32.uint_to_t (Prims.parse_int "0")));
(

let h1 = (FStar_HST.get ())
in ());
))





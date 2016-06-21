
open Prims

type ('Ah, 'Aa, 'Ab, 'Actr) willNotOverflow =
Prims.unit


type ('Ah0, 'Ah1, 'Aa, 'Actr) notModified =
Prims.unit


let fsum_index_aux : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  FStar_Buffer.u32  ->  Prims.unit = (fun a b ctr -> (

let h0 = (FStar_HST.get ())
in (

let ai = (FStar_Buffer.index a ctr)
in (

let bi = (FStar_Buffer.index b ctr)
in (

let z = (FStar_UInt64.add ai bi)
in (FStar_Buffer.upd a ctr z);
(

let h1 = (FStar_HST.get ())
in ());
)))))


type ('Ah0, 'Ah1, 'Aa, 'Ab, 'Actr) isSum =
Prims.unit


type ('Ah0, 'Ah1, 'Aa, 'Actr) notModified2 =
Prims.unit


let fsum_index_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Prims.unit = (fun h0 h1 h2 a b ctr -> ())


let rec fsum_index : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  FStar_Buffer.u32  ->  Prims.unit = (fun a b ctr -> (

let h0 = (FStar_HST.get ())
in (match ((FStar_UInt32.eq Curve_Parameters.nlength ctr)) with
| true -> begin
()
end
| uu____849 -> begin
(fsum_index_aux a b ctr);
(

let h1 = (FStar_HST.get ())
in (fsum_index a b (FStar_UInt32.add ctr (FStar_UInt32.uint_to_t (Prims.parse_int "1"))));
(

let h2 = (FStar_HST.get ())
in ());
);

end)))


let addition_lemma_aux : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.pos  ->  Prims.unit = (fun h0 h1 a b len -> ())


let rec addition_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Prims.unit = (fun h0 h1 a b len -> ())


let addition_max_value_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun h0 h1 a b c -> ())


let max_value_lemma : Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Prims.unit = (fun h a m -> ())


let addition_max_value_lemma_extended : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun h0 h1 a b c idx len -> ())


let auxiliary_lemma_2 : Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Prims.unit = (fun ha a hb b i -> ())


let auxiliary_lemma_0 : Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun ha a hb b -> ())


let auxiliary_lemma_1 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun h0 h1 b -> ())


let auxiliary_lemma_3 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun h0 h1 a b -> ())


let fsum' : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun a b -> (

let h0 = (FStar_HST.get ())
in (fsum_index a b (FStar_UInt32.uint_to_t (Prims.parse_int "0")));
(

let h1 = (FStar_HST.get ())
in ());
))





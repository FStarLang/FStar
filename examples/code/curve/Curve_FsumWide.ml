
open Prims

type u32 =
FStar_UInt32.t


let op_Plus_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.add


let op_Subtraction_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.sub


type ('Ah, 'Aa_idx, 'Ab_idx, 'Alen, 'Actr, 'Aa, 'Ab) willNotOverflow =
Prims.unit


type ('Ah0, 'Ah1, 'Aa_idx, 'Alen, 'Actr, 'Aa) isNotModified =
Prims.unit


type ('Ah0, 'Ah1, 'Aa_idx, 'Ab_idx, 'Alen, 'Actr, 'Aa, 'Ab) isSum =
Prims.unit


let fsum_index_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Prims.nat  ->  Curve_Bigint.bigint_wide  ->  Prims.nat  ->  Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun h0 h1 h2 a a_idx b b_idx len ctr -> ())


let rec fsum_index : Curve_Bigint.bigint_wide  ->  u32  ->  Curve_Bigint.bigint_wide  ->  u32  ->  u32  ->  u32  ->  Prims.unit = (fun a a_idx b b_idx len ctr -> (

let h0 = (FStar_HST.get ())
in (match ((FStar_UInt32.eq len ctr)) with
| true -> begin
()
end
| uu____1591 -> begin
(

let i = ctr
in (

let ai = (FStar_Buffer.index a (op_Plus_Bar i a_idx))
in (

let bi = (FStar_Buffer.index b (op_Plus_Bar i b_idx))
in (

let z = (FStar_UInt128.op_Plus_Hat ai bi)
in (FStar_Buffer.upd a (op_Plus_Bar a_idx i) z);
(

let h1 = (FStar_HST.get ())
in (fsum_index a a_idx b b_idx len (op_Plus_Bar ctr (FStar_UInt32.uint_to_t (Prims.parse_int "1"))));
(

let h2 = (FStar_HST.get ())
in ());
);
))))
end)))


let addition_lemma_aux : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.pos  ->  Prims.unit = (fun h0 h1 a b len -> ())


let rec addition_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.nat  ->  Prims.unit = (fun h0 h1 a b len -> ())


let addition_max_value_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 a b c -> ())


let max_value_lemma : Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Prims.nat  ->  Prims.unit = (fun h a m -> ())


let addition_max_value_lemma_extended : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun h0 h1 a b c idx len -> ())


let auxiliary_lemma_2 : Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Prims.nat  ->  Prims.unit = (fun ha a hb b i -> ())


let auxiliary_lemma_0 : Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun ha a hb b -> ())


let auxiliary_lemma_1 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 b -> ())


let auxiliary_lemma_3 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 a b -> ())


let fsum' : Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun a b -> (

let h0 = (FStar_HST.get ())
in (fsum_index a (FStar_UInt32.uint_to_t (Prims.parse_int "0")) b (FStar_UInt32.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength (FStar_UInt32.uint_to_t (Prims.parse_int "0")));
(

let h1 = (FStar_HST.get ())
in ());
))





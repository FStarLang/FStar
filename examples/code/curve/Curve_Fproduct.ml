
open Prims

let w : FStar_Buffer.u32  ->  Prims.int = FStar_UInt32.v


let vv : Curve_Bigint.u64  ->  Prims.int = FStar_UInt64.v


let op_Plus_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.add


let op_Subtraction_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.sub


let rec bitweight_lemma_1 : Curve_Bigint.template  ->  Prims.nat  ->  Prims.unit = (fun t i -> ())


let rec bitweight_lemma_0 : Curve_Bigint.template  ->  Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun t i j -> ())


let auxiliary_lemma_1 : Curve_Bigint.template  ->  Prims.nat  ->  Prims.nat  ->  Prims.unit = (Obj.magic ((fun t a b -> ())))


type ('Aha, 'Aa, 'Ahb, 'Ab, 'Alen) partialEquality =
Prims.unit


type ('Ahc, 'Ac, 'Aha, 'Aa, 'Ahb, 'Ab, 'Aa_idx, 'Alen) storesSum =
Prims.unit


let multiplication_step_lemma_1 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.nat  ->  Prims.pos  ->  Prims.unit = (fun h0 h1 a b c idx len -> ())


let multiplication_step_lemma_2 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.nat  ->  Prims.pos  ->  Prims.unit = (fun h0 h1 a b c idx len -> ())


let rec multiplication_step_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun h0 h1 a b c idx len -> ())


let max_limb : Prims.nat = (((Curve_Parameters.platform_wide - (Math_Lib.log_2 Curve_Parameters.norm_length)) - (Prims.parse_int "1")) / (Prims.parse_int "2"))


let max_wide : Prims.nat = (FStar_Mul.op_Star (Prims.parse_int "2") max_limb)


type ('Ah, 'Aa) fitsMaxLimbSize =
Prims.unit


let auxiliary_lemma_2 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun h0 h1 h2 a b ctr c -> ())


let auxiliary_lemma_3 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 h2 a b ctr c -> ())


type ('Aha, 'Aa, 'Ahb, 'Ab, 'Alen, 'Alen2) partialEquality2 =
Prims.unit


let rec auxiliary_lemma_5 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.int  ->  Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun h0 h1 a b c len len2 -> ())


type ('Ahc, 'Ac, 'Aha, 'Aa, 'As) isScalarProduct =
Prims.unit


let max_limb_lemma : Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun a b -> ())


let max_limb_lemma2 : Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Prims.nat  ->  Prims.unit = (Obj.magic ((fun h a b i ctr -> ())))


let is_scalar_product_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.u64  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 a s res -> ())


let multiplication_step_0 : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  FStar_Buffer.u32  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun a b ctr c tmp -> (

let h0 = (FStar_HST.get ())
in (

let s = (FStar_Buffer.index b ctr)
in (Curve_Fscalar.scalar_multiplication_tr tmp a s (FStar_UInt32.uint_to_t (Prims.parse_int "0")));
(

let h1 = (FStar_HST.get ())
in ());
)))


let std_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 a tmp -> ())


let max_wide_lemma : Prims.nat  ->  Prims.unit = (fun x -> ())


let lemma_helper_00 : Prims.unit  ->  Prims.unit = (fun uu____3200 -> ())


let lemma_helper_01 : Prims.int  ->  Prims.int  ->  Prims.int  ->  Prims.unit = (fun a b c -> ())


let lemma_helper_02 : Prims.nat  ->  Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun a b c -> ())


let multiplication_step_lemma_0010 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 a b ctr c tmp -> ())


let multiplication_step_lemma_001 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 a b ctr c tmp -> ())


let multiplication_step_lemma_01 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 a b ctr c tmp -> ())


let partial_equality_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Prims.nat  ->  Prims.unit = (fun h0 h1 c ctr -> ())


let lemma_helper_10 : Prims.nat  ->  Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun a b c -> ())


let max_value_lemma_1 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 h2 a b ctr c tmp -> ())


let max_value_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 h2 a b ctr c tmp -> ())


type ('Auu____5848, 'Auu____5849) modifies_2 =
((((Prims.unit, Prims.unit, Prims.unit) FStar_HyperHeap.modifies_just, (Prims.unit, Prims.unit, Prims.unit, Prims.unit) FStar_Buffer.modifies_buf) Prims.l_and, (Prims.unit, Prims.unit, Prims.unit, Prims.unit) FStar_Buffer.modifies_buf) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and


let standardized_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 h2 a c tmp -> ())


let length_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Prims.nat  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 h2 c ctr tmp -> ())


let lemma_helper_20 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 h2 a b ctr c tmp -> ())


let multiplication_step_lemma_02 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  FStar_Buffer.u32  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 h2 a b ctr c tmp -> ())


let multiplication_step_p1 : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  FStar_Buffer.u32  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun a b ctr c tmp -> (

let h0 = (FStar_HST.get ())
in (multiplication_step_0 a b ctr c tmp);
(

let h1 = (FStar_HST.get ())
in (Curve_FsumWide.fsum_index c ctr tmp (FStar_UInt32.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength (FStar_UInt32.uint_to_t (Prims.parse_int "0")));
(

let h2 = (FStar_HST.get ())
in ());
);
))


let helper_lemma_6 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 a b ctr c tmp -> ())


let multiplication_step : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  FStar_Buffer.u32  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun a b ctr c tmp -> (

let h0 = (FStar_HST.get ())
in (multiplication_step_p1 a b ctr c tmp);
(

let h1 = (FStar_HST.get ())
in ());
))


let multiplication_step_lemma_03 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.pos  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 a b ctr c -> ())


let helper_lemma_7 : Prims.pos  ->  Prims.unit = (fun ctr -> ())


let multiplication_aux_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.pos  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 a b ctr c tmp -> ())


let multiplication_aux_lemma_2 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.nat  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 h2 a b ctr c tmp -> ())


let rec multiplication_aux : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  FStar_Buffer.u32  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun a b ctr c tmp -> (

let h0 = (FStar_HST.get ())
in (match ((FStar_UInt32.eq ctr (FStar_UInt32.uint_to_t (Prims.parse_int "0")))) with
| true -> begin
()
end
| uu____12423 -> begin
(multiplication_step a b (op_Subtraction_Bar Curve_Parameters.nlength ctr) c tmp);
(

let h1 = (FStar_HST.get ())
in (multiplication_aux a b (op_Subtraction_Bar ctr (FStar_UInt32.uint_to_t (Prims.parse_int "1"))) c tmp);
(

let h2 = (FStar_HST.get ())
in ());
);

end)))


let helper_lemma_13 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun h0 h1 a -> ())


let helper_lemma_15 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 c -> ())


let multiplication_lemma_1 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun h0 h1 c a b -> ())


let helper_lemma_14 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 h2 c tmp -> ())


let multiplication_lemma_2 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 h2 c a b tmp -> ())


let multiplication : Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun c a b -> (

let h0 = (FStar_HST.get ())
in (

let tmp = (FStar_Buffer.create (FStar_UInt128.of_string "0") Curve_Parameters.nlength)
in (

let h1 = (FStar_HST.get ())
in (multiplication_aux a b Curve_Parameters.nlength c tmp);
(

let h2 = (FStar_HST.get ())
in ());
))))





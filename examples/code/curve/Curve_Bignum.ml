
open Prims

let w : FStar_Buffer.u32  ->  Prims.int = FStar_UInt32.v


let vv : Curve_Bigint.u128  ->  Prims.int = FStar_UInt128.v


let op_Plus_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.add


let op_Subtraction_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.sub


type heap =
FStar_HyperStack.mem


let nat_to_felem : Prims.nat  ->  Math_Field.felem = (Obj.magic ((fun x -> ())))


let felem_to_nat : Math_Field.felem  ->  Prims.nat = (Obj.magic ((fun __48 -> ())))


let finite_field_implementation : Prims.nat  ->  Prims.unit = (fun x -> ())


let felem_lemma : Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun x y -> ())


let valueOf : heap  ->  Curve_Bigint.bigint  ->  Math_Field.felem = (Obj.magic ((fun h b -> ())))


let valueOf_wide : heap  ->  Curve_Bigint.bigint_wide  ->  Math_Field.felem = (Obj.magic ((fun h b -> ())))


type ('Aha, 'Aa, 'Ahb, 'Ab) eq =
(((Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.live, (Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.live) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and


type ('Aha, 'Aa, 'Ahb, 'Ab) eq_wide_r =
(((Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.live, (Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and


type ('Aha, 'Aa, 'Ahb, 'Ab) eq_wide_l =
(((Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live, (Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.live) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and


type ('Aha, 'Aa, 'Ahb, 'Ab) eq_wide =
(((Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live, (Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and


let valueOfBytes : heap  ->  Curve_Bigint.bytes  ->  Prims.nat = (fun h b -> (Obj.magic (())))


let cast_lemma_1 : Curve_Bigint.u128  ->  Prims.unit = (fun x -> ())


let rec copy_to_bigint' : Curve_Bigint.bigint  ->  Curve_Bigint.bigint_wide  ->  FStar_Buffer.u32  ->  FStar_Buffer.u32  ->  FStar_Buffer.u32  ->  Prims.unit = (fun output b idx len ctr -> (

let h0 = (FStar_HST.get ())
in (match ((FStar_UInt32.eq len ctr)) with
| true -> begin
()
end
| uu____443 -> begin
(

let bi = (FStar_Buffer.index b (op_Plus_Bar idx ctr))
in (

let cast = (FStar_Int_Cast.uint128_to_uint64 bi)
in (FStar_Buffer.upd output (op_Plus_Bar idx ctr) cast);
(

let h1 = (FStar_HST.get ())
in (copy_to_bigint' output b idx len (op_Plus_Bar ctr (FStar_UInt32.uint_to_t (Prims.parse_int "1")))));
))
end)))


let norm_bigint_lemma_1 : heap  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h b -> ())


let copy_to_bigint : Curve_Bigint.bigint  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun output b -> (

let h0 = (FStar_HST.get ())
in (copy_to_bigint' output b (FStar_UInt32.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength (FStar_UInt32.uint_to_t (Prims.parse_int "0")));
(

let h1 = (FStar_HST.get ())
in ());
))


let rec copy_to_bigint_wide' : Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint  ->  FStar_Buffer.u32  ->  FStar_Buffer.u32  ->  FStar_Buffer.u32  ->  Prims.unit = (fun output b idx len ctr -> (

let h0 = (FStar_HST.get ())
in (match ((FStar_UInt32.eq len ctr)) with
| true -> begin
()
end
| uu____1325 -> begin
(

let bi = (FStar_Buffer.index b (op_Plus_Bar idx ctr))
in (

let cast = (FStar_Int_Cast.uint64_to_uint128 bi)
in (FStar_Buffer.upd output (op_Plus_Bar idx ctr) cast);
(

let h1 = (FStar_HST.get ())
in (copy_to_bigint_wide' output b idx len (op_Plus_Bar ctr (FStar_UInt32.uint_to_t (Prims.parse_int "1")))));
))
end)))


let copy_to_bigint_wide : Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun output b -> (

let h0 = (FStar_HST.get ())
in (copy_to_bigint_wide' output b (FStar_UInt32.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength (FStar_UInt32.uint_to_t (Prims.parse_int "0")));
(

let h1 = (FStar_HST.get ())
in ());
))


let copy_lemma : heap  ->  heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun h0 h1 a b -> ())


let rec erase : Curve_Bigint.bigint  ->  FStar_Buffer.u32  ->  FStar_Buffer.u32  ->  FStar_Buffer.u32  ->  Prims.unit = (fun b idx len ctr -> (

let h0 = (FStar_HST.get ())
in (match ((FStar_UInt32.eq len ctr)) with
| true -> begin
()
end
| uu____2005 -> begin
(FStar_Buffer.upd b (op_Plus_Bar idx ctr) (FStar_UInt64.uint_to_t (Prims.parse_int "0")));
(

let h1 = (FStar_HST.get ())
in (erase b idx len (op_Plus_Bar ctr (FStar_UInt32.uint_to_t (Prims.parse_int "1")))));

end)))


let rec erase_wide : Curve_Bigint.bigint_wide  ->  FStar_Buffer.u32  ->  FStar_Buffer.u32  ->  FStar_Buffer.u32  ->  Prims.unit = (fun b idx len ctr -> (

let h0 = (FStar_HST.get ())
in (match ((FStar_UInt32.eq len ctr)) with
| true -> begin
()
end
| uu____2220 -> begin
(FStar_Buffer.upd b (op_Plus_Bar idx ctr) (FStar_UInt128.of_string "0"));
(

let h1 = (FStar_HST.get ())
in (erase_wide b idx len (op_Plus_Bar ctr (FStar_UInt32.uint_to_t (Prims.parse_int "1")))));

end)))


type ('Auu____2359, 'Auu____2360) modifies_2 =
((((Prims.unit, Prims.unit, Prims.unit) FStar_HyperHeap.modifies_just, (Prims.unit, Prims.unit, Prims.unit, Prims.unit) FStar_Buffer.modifies_buf) Prims.l_and, (Prims.unit, Prims.unit, Prims.unit, Prims.unit) FStar_Buffer.modifies_buf) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and


let modulo : Curve_Bigint.bigint  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun output b -> (

let h0 = (FStar_HST.get ())
in (Curve_Modulo.freduce_degree b);
(Curve_Modulo.freduce_coefficients b);
(

let h = (FStar_HST.get ())
in (copy_to_bigint output b));
))


let fsum_lemma : heap  ->  heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (Obj.magic ((fun h0 h1 res a b -> ())))


let fsum : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun a b -> (FStar_HST.push_frame ());
(

let h0 = (FStar_HST.get ())
in (Curve_Fsum.fsum' a b);
(

let tmp = (FStar_Buffer.create (FStar_UInt128.of_string "0") (FStar_UInt32.uint_to_t (Prims.parse_int "9")))
in (

let h1 = (FStar_HST.get ())
in (copy_to_bigint_wide tmp a);
(

let h2 = (FStar_HST.get ())
in (modulo a tmp);
(

let h1 = (FStar_HST.get ())
in (FStar_HST.pop_frame ()));
);
));
);
)


let fdifference_lemma : heap  ->  heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (Obj.magic ((fun h0 h1 res a b -> ())))


let fdifference : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun a b -> (FStar_HST.push_frame ());
(

let h0 = (FStar_HST.get ())
in (

let b' = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (FStar_Buffer.blit b (FStar_UInt32.uint_to_t (Prims.parse_int "0")) b' (FStar_UInt32.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength);
(

let h1 = (FStar_HST.get ())
in (Curve_Modulo.add_big_zero b');
(

let h2 = (FStar_HST.get ())
in (Curve_Fdifference.fdifference' a b');
(

let h3 = (FStar_HST.get ())
in (

let tmp = (FStar_Buffer.create (FStar_UInt128.of_string "0") (op_Subtraction_Bar (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.parse_int "2")) Curve_Parameters.nlength) (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (

let h4 = (FStar_HST.get ())
in (copy_to_bigint_wide tmp a);
(

let h5 = (FStar_HST.get ())
in (modulo a tmp);
(

let h6 = (FStar_HST.get ())
in (FStar_HST.pop_frame ()));
);
)));
);
);
));
)


let fscalar : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Curve_Bigint.u64  ->  Prims.unit = (fun res b s -> (FStar_HST.push_frame ());
(

let h0 = (FStar_HST.get ())
in (

let tmp = (FStar_Buffer.create (FStar_UInt128.of_string "0") (op_Subtraction_Bar (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.parse_int "2")) Curve_Parameters.nlength) (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (Curve_Fscalar.scalar' tmp b s);
(

let h = (FStar_HST.get ())
in (modulo res tmp);
(

let h1 = (FStar_HST.get ())
in (FStar_HST.pop_frame ()));
);
));
)


let norm_lemma_2 : heap  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun h b -> ())


let fmul_lemma : heap  ->  heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (Obj.magic ((fun h0 h1 res a b -> ())))


let fmul : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun res a b -> (FStar_HST.push_frame ());
(

let h0 = (FStar_HST.get ())
in (

let tmp = (FStar_Buffer.create (FStar_UInt128.of_string "0") (op_Subtraction_Bar (FStar_UInt32.mul (FStar_UInt32.uint_to_t (Prims.parse_int "2")) Curve_Parameters.nlength) (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (

let h1 = (FStar_HST.get ())
in (Curve_Fproduct.multiplication tmp a b);
(

let h2 = (FStar_HST.get ())
in (modulo res tmp);
(

let h3 = (FStar_HST.get ())
in (FStar_HST.pop_frame ()));
);
)));
)


let fsquare : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun res a -> (fmul res a a))






open Prims

let w : FStar_Buffer.u32  ->  Prims.int = FStar_UInt32.v


let vv : Curve_Bigint.u128  ->  Prims.int = FStar_UInt128.v


let op_Plus_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.add


let op_Subtraction_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.sub


type heap =
FStar_HyperStack.mem


let op_Plus_Star : Prims.nat  ->  Math_Curve.celem  ->  Math_Curve.celem = (fun n x -> (Obj.magic (())))


let op_Plus_Plus_Plus = (fun a b -> (FStar_Set.union a b))


let op_Plus_Star_Plus = (Obj.magic ((fun x y -> ())))


type ('An, 'Aq, 'Ah, 'Ap, 'Ap') nTimesQ =
((((Prims.unit, Prims.unit) Curve_Point.onCurve, (Prims.unit, Prims.unit) Curve_Point.onCurve) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and


let formula_0 : Prims.nat FStar_Ghost.erased  ->  Curve_Bigint.u8  ->  Prims.nat FStar_Ghost.erased = (Obj.magic ((fun scalar byte -> (Obj.magic (())))))


let formula_1 : Prims.nat FStar_Ghost.erased  ->  Curve_Bigint.u8  ->  Prims.nat FStar_Ghost.erased = (Obj.magic ((fun n b -> (Obj.magic (())))))


let formula_2 : Prims.nat  ->  Curve_Bigint.u8  ->  Prims.nat FStar_Ghost.erased = (Obj.magic ((fun n b -> ())))


let eformula_2 : Prims.nat FStar_Ghost.erased  ->  Curve_Bigint.u8  ->  Prims.nat FStar_Ghost.erased = (Obj.magic ((fun n b -> ())))


let mk_mask : Curve_Bigint.u8  ->  Curve_Bigint.u64 = (fun x -> (

let y = (FStar_Int_Cast.uint8_to_uint64 x)
in (FStar_UInt64.sub_mod (FStar_UInt64.uint_to_t (Prims.parse_int "0")) y)))


let small_step_exit : Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Prims.nat FStar_Ghost.erased  ->  Curve_Bigint.u8  ->  Prims.nat FStar_Ghost.erased  ->  Prims.unit = (Obj.magic ((fun pp ppq p pq q n byte scalar -> (

let h0 = (FStar_HST.get ())
in (Curve_Point.copy2 pp ppq p pq);
(

let h1 = (FStar_HST.get ())
in ());
))))


let nth_bit : Curve_Bigint.u8  ->  FStar_Buffer.u32  ->  Curve_Bigint.u8 = (fun byte idx -> (

let bit = (FStar_UInt8.logand (FStar_UInt8.shift_right byte (op_Subtraction_Bar (FStar_UInt32.uint_to_t (Prims.parse_int "7")) idx)) (FStar_UInt8.uint_to_t (Prims.parse_int "1")))
in bit))


let double_and_add_lemma_1 : Math_Curve.celem  ->  Prims.nat FStar_Ghost.erased  ->  Prims.nat FStar_Ghost.erased  ->  Prims.unit = (Obj.magic ((fun q n m -> ())))


let small_step_core_lemma_1 : heap  ->  heap  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Prims.unit = (fun h0 h1 pp ppq p pq q -> ())


let gsmall_step_core_lemma_3 = (Obj.magic ((fun h0 h h2 h1 pp ppq p pq q n ctr byt scalar -> ())))


let small_step_core : Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Prims.nat FStar_Ghost.erased  ->  FStar_Buffer.u32  ->  Curve_Bigint.u8  ->  Prims.nat FStar_Ghost.erased  ->  Prims.unit = (((fun pp ppq p pq q n ctr b scalar -> (

let h0 = (FStar_HST.get ())
in (

let bit = (nth_bit b ctr)
in (

let mask = (mk_mask bit)
in (Curve_Point.swap_conditional p pq mask);
(

let h = (FStar_HST.get ())
in (Curve_AddAndDouble.double_and_add pp ppq p pq q);
(

let h2 = (FStar_HST.get ())
in (Curve_Point.swap_conditional pp ppq mask);
(

let h1 = (FStar_HST.get ())
in ());
);
);
))))))


let small_step_lemma_1 : heap  ->  heap  ->  heap  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Prims.unit = (fun h0 h1 h2 pp ppq p pq q -> ())


let small_step_lemma_2 : heap  ->  heap  ->  heap  ->  heap  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Prims.unit = (fun h0 h1 h2 h3 pp ppq p pq q -> ())


let rec small_step : Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Prims.nat FStar_Ghost.erased  ->  FStar_Buffer.u32  ->  Curve_Bigint.u8  ->  Prims.nat FStar_Ghost.erased  ->  Prims.unit = (((fun pp ppq p pq q n ctr b scalar -> (match ((FStar_UInt32.eq (FStar_UInt32.uint_to_t (Prims.parse_int "8")) ctr)) with
| true -> begin
()
end
| uu____26312 -> begin
(

let h0 = (FStar_HST.get ())
in (small_step_core pp ppq p pq q (Obj.magic ((Obj.magic (())))) ctr b (Obj.magic ((Obj.magic (())))));
(

let h1 = (FStar_HST.get ())
in (

let bit = (nth_bit b ctr)
in (Curve_Point.swap_both pp ppq p pq);
(

let h2 = (FStar_HST.get ())
in (small_step pp ppq p pq q (Obj.magic ((Obj.magic (())))) (op_Plus_Bar ctr (FStar_UInt32.uint_to_t (Prims.parse_int "1"))) b (Obj.magic ((Obj.magic (())))));
(

let h3 = (FStar_HST.get ())
in ());
);
));
)
end))))


let formula_4 : heap  ->  Curve_Bigint.bytes  ->  Prims.nat  ->  Prims.nat FStar_Ghost.erased = (Obj.magic ((fun h n ctr -> ())))


type ('An, 'Ap) distinct2 =
Prims.l_True


let gbig_step_lemma_1 : heap  ->  Curve_Point.heap  ->  Curve_Bigint.bytes  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Prims.nat  ->  Curve_Bigint.u8  ->  Prims.unit = (fun h0 h1 n pp ppq p pq q ctr b -> ())


let big_step_lemma_2 : heap  ->  heap  ->  heap  ->  Curve_Bigint.bytes  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Prims.nat  ->  Curve_Bigint.u8  ->  Prims.unit = (fun h0 h1 h2 n pp ppq p pq q ctr byte -> ())


let rec big_step : Curve_Bigint.bytes  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  Curve_Point.point  ->  FStar_Buffer.u32  ->  Prims.unit = (fun n pp ppq p pq q ctr -> (

let h0 = (FStar_HST.get ())
in (match ((FStar_UInt32.eq Curve_Parameters.blength ctr)) with
| true -> begin
()
end
| uu____42228 -> begin
(

let byte = (FStar_Buffer.index n (op_Subtraction_Bar (op_Subtraction_Bar Curve_Parameters.blength (FStar_UInt32.uint_to_t (Prims.parse_int "1"))) ctr))
in (

let m = (Obj.magic (()))
in (small_step pp ppq p pq q (Obj.magic ((Obj.magic (())))) (FStar_UInt32.uint_to_t (Prims.parse_int "0")) byte (Obj.magic ((Obj.magic (())))));
(

let h1 = (FStar_HST.get ())
in (big_step n pp ppq p pq q (op_Plus_Bar ctr (FStar_UInt32.uint_to_t (Prims.parse_int "1"))));
(

let h2 = (FStar_HST.get ())
in ());
);
))
end)))


let montgomery_ladder : Curve_Point.point  ->  Curve_Bigint.bytes  ->  Curve_Point.point  ->  Prims.unit = (fun res n q -> (

let two_p_x = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) (op_Plus_Bar Curve_Parameters.nlength (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (

let two_p_y = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (

let two_p_z = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) (op_Plus_Bar Curve_Parameters.nlength (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (

let two_p = (Curve_Point.make two_p_x two_p_y two_p_z)
in (

let two_p_plus_q_x = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) (op_Plus_Bar Curve_Parameters.nlength (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (

let two_p_plus_q_y = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (

let two_p_plus_q_z = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) (op_Plus_Bar Curve_Parameters.nlength (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (

let two_p_plus_q = (Curve_Point.make two_p_plus_q_x two_p_plus_q_y two_p_plus_q_z)
in (

let p_x = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (FStar_Buffer.blit (Curve_Point.get_x q) (FStar_UInt32.uint_to_t (Prims.parse_int "0")) p_x (FStar_UInt32.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength);
(

let p_y = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (FStar_Buffer.blit (Curve_Point.get_y q) (FStar_UInt32.uint_to_t (Prims.parse_int "0")) p_y (FStar_UInt32.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength);
(

let p_z = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (FStar_Buffer.blit (Curve_Point.get_z q) (FStar_UInt32.uint_to_t (Prims.parse_int "0")) p_z (FStar_UInt32.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength);
(

let p = (Curve_Point.make p_x p_y p_z)
in (

let inf_x = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) (op_Plus_Bar Curve_Parameters.nlength (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (FStar_Buffer.upd inf_x (FStar_UInt32.uint_to_t (Prims.parse_int "0")) (FStar_UInt64.uint_to_t (Prims.parse_int "1")));
(

let inf_y = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength)
in (

let inf_z = (FStar_Buffer.create (FStar_UInt64.uint_to_t (Prims.parse_int "0")) (op_Plus_Bar Curve_Parameters.nlength (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (

let inf = (Curve_Point.make inf_x inf_y inf_z)
in (big_step n two_p two_p_plus_q inf p q (FStar_UInt32.uint_to_t (Prims.parse_int "0")));
(Curve_Point.copy res two_p);
)));
));
);
);
))))))))))





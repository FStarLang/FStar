
open Prims

let w : FStar_Buffer.u32  ->  Prims.int = FStar_UInt32.v


let vv : Curve_Bigint.u64  ->  Prims.int = FStar_UInt64.v


let op_Plus_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.add


let op_Subtraction_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.sub


type heap =
FStar_HyperStack.mem


let op_Bar_Amp : FStar_UInt128.t  ->  FStar_UInt128.t  ->  FStar_UInt128.t = (fun x y -> (FStar_UInt128.logand x y))


let op_Bar_Greater_Greater : FStar_UInt128.t  ->  FStar_UInt32.t  ->  FStar_UInt128.t = (fun x y -> (FStar_UInt128.shift_right x y))


let op_Bar_Less_Less : FStar_UInt128.t  ->  FStar_UInt32.t  ->  FStar_UInt128.t = (fun x y -> (FStar_UInt128.shift_left x y))


let op_Bar_Plus : FStar_UInt128.t  ->  FStar_UInt128.t  ->  FStar_UInt128.t = (fun x y -> (FStar_UInt128.add x y))


let op_Bar_Star : FStar_UInt128.t  ->  FStar_UInt128.t  ->  FStar_UInt128.t = (fun x y -> (FStar_UInt128.mul x y))


let prime_modulo_lemma : Prims.unit  ->  Prims.unit = (fun __111 -> ())


let modulo_lemma : Prims.nat  ->  Prims.pos  ->  Prims.unit = (fun a b -> ())


let pow2_4_lemma : Prims.unit  ->  Prims.unit = (fun uu____127 -> ())


let pow2_5_lemma : Prims.unit  ->  Prims.unit = (fun uu____131 -> ())


let satisfies_modulo_constraints : Curve_Bigint.heap  ->  Curve_Bigint.u128 FStar_Buffer.buffer  ->  Prims.bool = (fun h b -> (Obj.magic (())))


type ('Ah, 'Ab) satisfiesModuloConstraints =
((Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live, Prims.unit Prims.b2t) Prims.l_and


let times_19 : Curve_Bigint.u128  ->  Curve_Bigint.u128 = (fun x -> (

let y = (op_Bar_Less_Less x (FStar_UInt32.uint_to_t (Prims.parse_int "4")))
in (

let z = (op_Bar_Less_Less x (FStar_UInt32.uint_to_t (Prims.parse_int "1")))
in (op_Bar_Plus (op_Bar_Plus x y) z))))


type ('Ah, 'Ab, 'Actr) reducible =
(((Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live, Prims.unit Prims.b2t) Prims.l_and, Prims.unit) Prims.l_and


type ('Ah, 'Ab, 'Actr) reducible' =
(((Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live, Prims.unit Prims.b2t) Prims.l_and, Prims.unit) Prims.l_and


type ('Ah0, 'Ah1, 'Ab, 'Actr) times19 =
(((((Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live, (Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and, Prims.unit) Prims.l_and


type ('Ah0, 'Ah1, 'Ab, 'Actr) times19' =
(((((Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live, (Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and, Prims.unit) Prims.l_and


type ('Ah0, 'Ah1, 'Ab, 'Actr) untouched =
(((((Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live, (Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and, Prims.unit) Prims.l_and


type ('Ah0, 'Ah1, 'Ab, 'Actr) untouched' =
(((((Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live, (Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and, Prims.unit) Prims.l_and


let lemma_helper_00 : Prims.nat  ->  Prims.unit = (fun ctr -> ())


let lemma_helper_01 : Prims.nat  ->  Prims.unit = (fun ctr -> ())


let rec lemma_helper_02 : Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun a b -> ())


let lemma_helper_03 : Prims.nat  ->  Prims.unit = (Obj.magic ((fun ctr -> ())))


let lemma_helper_04 : Prims.nat  ->  Prims.unit = (fun ctr -> ())


let rec pow2_bitweight_lemma_1 : Prims.pos  ->  Prims.unit = (fun ctr -> ())


let bitweight_norm_length_lemma : Prims.unit  ->  Prims.unit = (fun uu____889 -> ())


let lemma_helper_10 : heap  ->  Curve_Bigint.bigint_wide  ->  Prims.pos  ->  Prims.unit = (fun h0 b ctr -> ())


let lemma_helper_12 : Prims.int  ->  Prims.int  ->  Prims.int  ->  Prims.unit = (fun a b c -> ())


let lemma_helper_11 : heap  ->  heap  ->  Curve_Bigint.bigint_wide  ->  Prims.pos  ->  Prims.pos  ->  Prims.unit = (fun h0 h1 b ctr prime -> ())


let freduce_degree_lemma_2 : heap  ->  heap  ->  Curve_Bigint.bigint_wide  ->  Prims.pos  ->  Prims.unit = (Obj.magic ((fun h0 h1 b ctr -> ())))


let freduce_degree_lemma : heap  ->  heap  ->  Curve_Bigint.bigint_wide  ->  Prims.nat  ->  Prims.unit = (Obj.magic ((fun h0 h1 b ctr -> ())))


let rec freduce_degree' : Curve_Bigint.bigint_wide  ->  FStar_Buffer.u32  ->  Prims.unit = (fun b ctr' -> (

let h0 = (FStar_HST.get ())
in (match ((FStar_UInt32.eq ctr' (FStar_UInt32.uint_to_t (Prims.parse_int "0")))) with
| true -> begin
(

let b5ctr = (FStar_Buffer.index b Curve_Parameters.nlength)
in (

let bctr = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "0")))
in (

let b5ctr = (times_19 b5ctr)
in (

let bctr = (op_Bar_Plus bctr b5ctr)
in (FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "0")) bctr);
(

let h1 = (FStar_HST.get ())
in ());
))))
end
| uu____3197 -> begin
(

let ctr = ctr'
in (

let b5ctr = (FStar_Buffer.index b (op_Plus_Bar ctr Curve_Parameters.nlength))
in (

let bctr = (FStar_Buffer.index b ctr)
in (

let b5ctr = (times_19 b5ctr)
in (

let bctr = (op_Bar_Plus bctr b5ctr)
in (FStar_Buffer.upd b ctr bctr);
(

let h1 = (FStar_HST.get ())
in (freduce_degree' b (op_Subtraction_Bar ctr (FStar_UInt32.uint_to_t (Prims.parse_int "1"))));
(

let h2 = (FStar_HST.get ())
in ());
);
)))))
end)))


let aux_lemma_4 : heap  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (Obj.magic ((fun h b -> ())))


let aux_lemma_5 : heap  ->  heap  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (Obj.magic ((fun h0 h1 b -> ())))


let freduce_degree : Curve_Bigint.bigint_wide  ->  Prims.unit = (fun b -> (

let h0 = (FStar_HST.get ())
in (freduce_degree' b (op_Subtraction_Bar Curve_Parameters.nlength (FStar_UInt32.uint_to_t (Prims.parse_int "2"))));
(

let h1 = (FStar_HST.get ())
in ());
))


let pow2_bitweight_lemma : Prims.nat  ->  Prims.unit = (Obj.magic ((fun ctr -> ())))


let eval_carry_lemma : heap  ->  Curve_Bigint.bigint_wide  ->  heap  ->  Curve_Bigint.bigint_wide  ->  Prims.nat  ->  Prims.unit = (fun ha a hb b ctr -> ())


let gauxiliary_lemma_1 = (fun bip1 c -> ())


let mod_lemma_1 : Prims.nat  ->  Prims.pos  ->  Prims.unit = (fun a b -> ())


let mod2_51 : Curve_Bigint.u128  ->  Curve_Bigint.u128 = (fun a -> (

let mask = (op_Bar_Less_Less (FStar_UInt128.of_string "1") (FStar_UInt32.uint_to_t (Prims.parse_int "51")))
in (

let mask = (FStar_UInt128.sub mask (FStar_UInt128.of_string "1"))
in (

let res = (op_Bar_Amp a mask)
in res))))


type ('Ah, 'Ab, 'Actr) carriable =
(((Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live, Prims.unit Prims.b2t) Prims.l_and, Prims.unit) Prims.l_and


type ('Ah1, 'Ab, 'Actr) carried =
(((((Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live, Prims.unit Prims.b2t) Prims.l_and, Prims.unit) Prims.l_and, (Prims.unit Prims.b2t, Prims.unit Prims.b2t) Prims.l_imp) Prims.l_and, (Prims.unit Prims.b2t, Prims.unit Prims.b2t) Prims.l_imp) Prims.l_and


type ('Ah1, 'Ab, 'Actr) carried' =
((((Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live, Prims.unit Prims.b2t) Prims.l_and, Prims.unit) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and


type ('Ah0, 'Ah1, 'Ab, 'Actr) untouched_2 =
(((((Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live, (Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and, Prims.unit) Prims.l_and


let rec carry : Curve_Bigint.bigint_wide  ->  FStar_Buffer.u32  ->  Prims.unit = (fun b i -> (

let h0 = (FStar_HST.get ())
in (match ((FStar_UInt32.eq i Curve_Parameters.nlength)) with
| true -> begin
()
end
| uu____4978 -> begin
(

let bi = (FStar_Buffer.index b i)
in (

let ri = (mod2_51 bi)
in (FStar_Buffer.upd b i ri);
(

let h1 = (FStar_HST.get ())
in (

let c = (op_Bar_Greater_Greater bi (FStar_UInt32.uint_to_t (Prims.parse_int "51")))
in (

let bip1 = (FStar_Buffer.index b (op_Plus_Bar i (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (

let z = (op_Bar_Plus bip1 c)
in (FStar_Buffer.upd b (op_Plus_Bar i (FStar_UInt32.uint_to_t (Prims.parse_int "1"))) z);
(

let h2 = (FStar_HST.get ())
in (carry b (op_Plus_Bar i (FStar_UInt32.uint_to_t (Prims.parse_int "1")))));
))));
))
end)))


let carry_top_to_0 : Curve_Bigint.bigint_wide  ->  Prims.unit = (fun b -> (

let h0 = (FStar_HST.get ())
in (

let b0 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "0")))
in (

let btop = (FStar_Buffer.index b Curve_Parameters.nlength)
in (

let btop_19 = (times_19 btop)
in (FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "0")) (op_Bar_Plus b0 btop_19));
(

let h1 = (FStar_HST.get ())
in ());
)))))


type ('Ah, 'Ab, 'Actr) carriable2 =
(((((((((Curve_Bigint.u128, Prims.unit, Prims.unit) FStar_Buffer.live, Prims.unit Prims.b2t) Prims.l_and, Prims.unit) Prims.l_and, Prims.unit) Prims.l_and, (Prims.unit Prims.b2t, Prims.unit Prims.b2t) Prims.l_imp) Prims.l_and, (Prims.unit Prims.b2t, Prims.unit Prims.b2t) Prims.l_imp) Prims.l_and, Prims.unit Prims.b2t) Prims.l_and, (Prims.unit Prims.b2t, Prims.unit) Prims.l_imp) Prims.l_and, ((Prims.unit Prims.b2t, Prims.unit Prims.b2t) Prims.l_and, Prims.unit) Prims.l_imp) Prims.l_and


let helper_lemma_20 : Curve_Bigint.u128  ->  Curve_Bigint.u128  ->  Prims.unit = (fun a b -> ())


let helper_lemma_21 : Curve_Bigint.u128  ->  Prims.unit = (fun a -> ())


let rec carry2 : Curve_Bigint.bigint_wide  ->  FStar_Buffer.u32  ->  Prims.unit = (fun b i -> (

let h0 = (FStar_HST.get ())
in (match ((FStar_UInt32.eq i Curve_Parameters.nlength)) with
| true -> begin
()
end
| uu____6021 -> begin
(

let bi = (FStar_Buffer.index b i)
in (

let ri = (mod2_51 bi)
in (FStar_Buffer.upd b i ri);
(

let h1 = (FStar_HST.get ())
in (

let bip1 = (FStar_Buffer.index b (op_Plus_Bar i (FStar_UInt32.uint_to_t (Prims.parse_int "1"))))
in (

let c = (op_Bar_Greater_Greater bi (FStar_UInt32.uint_to_t (Prims.parse_int "51")))
in (

let z = (op_Bar_Plus bip1 c)
in (FStar_Buffer.upd b (op_Plus_Bar i (FStar_UInt32.uint_to_t (Prims.parse_int "1"))) z);
(

let h2 = (FStar_HST.get ())
in (carry2 b (op_Plus_Bar i (FStar_UInt32.uint_to_t (Prims.parse_int "1")))));
))));
))
end)))


let helper_lemma_30 : Curve_Bigint.u128  ->  Curve_Bigint.u128  ->  Prims.unit = (fun a b -> ())


let helper_lemma_32 : Curve_Bigint.u128  ->  Prims.unit = (fun a -> ())


let helper_lemma_33 : Curve_Bigint.u128  ->  Curve_Bigint.u128  ->  Prims.unit = (fun a b -> ())


let last_carry : Curve_Bigint.bigint_wide  ->  Prims.unit = (fun b -> (

let h0 = (FStar_HST.get ())
in (

let b0 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "0")))
in (

let btop = (FStar_Buffer.index b Curve_Parameters.nlength)
in (

let btop_19 = (times_19 btop)
in (

let bi = (op_Bar_Plus b0 btop_19)
in (FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "0")) bi);
(

let h1 = (FStar_HST.get ())
in (FStar_Buffer.upd b Curve_Parameters.nlength (FStar_UInt128.of_string "0"));
(

let h2 = (FStar_HST.get ())
in (

let ri = (mod2_51 bi)
in (FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "0")) ri);
(

let h3 = (FStar_HST.get ())
in (

let c = (op_Bar_Greater_Greater bi (FStar_UInt32.uint_to_t (Prims.parse_int "51")))
in (

let bip1 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "1")))
in (

let z = (op_Bar_Plus bip1 c)
in (FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "1")) z);
(

let h4 = (FStar_HST.get ())
in ());
))));
));
);
))))))


let lemma_helper_40 : heap  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h b -> ())


let lemma_helper_41 : Curve_Bigint.u128  ->  Prims.unit = (fun a -> ())


let lemma_helper_42 : Curve_Bigint.u128  ->  Curve_Bigint.u128  ->  Prims.unit = (fun a b -> ())


let freduce_coefficients : Curve_Bigint.bigint_wide  ->  Prims.unit = (fun b -> (

let h = (FStar_HST.get ())
in (FStar_Buffer.upd b Curve_Parameters.nlength (FStar_UInt128.of_string "0"));
(

let h' = (FStar_HST.get ())
in (carry b (FStar_UInt32.uint_to_t (Prims.parse_int "0")));
(

let h = (FStar_HST.get ())
in (carry_top_to_0 b);
(

let h1 = (FStar_HST.get ())
in (FStar_Buffer.upd b Curve_Parameters.nlength (FStar_UInt128.of_string "0"));
(

let h2 = (FStar_HST.get ())
in (

let b0 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "0")))
in (

let b1 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "1")))
in (

let r0 = (mod2_51 b0)
in (

let c0 = (op_Bar_Greater_Greater b0 (FStar_UInt32.uint_to_t (Prims.parse_int "51")))
in (

let h = (FStar_HST.get ())
in (FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "0")) r0);
(FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "1")) (op_Bar_Plus b1 c0));
(

let h' = (FStar_HST.get ())
in (carry2 b (FStar_UInt32.uint_to_t (Prims.parse_int "1")));
(last_carry b);
);
))))));
);
);
);
))


let addition_lemma : Curve_Bigint.u64  ->  Prims.nat  ->  Curve_Bigint.u64  ->  Prims.nat  ->  Prims.unit = (fun a m b n -> ())


let aux_lemma_1 : Prims.unit  ->  Prims.unit = (fun uu____8237 -> ())


let add_big_zero_core : Curve_Bigint.bigint  ->  Prims.unit = (fun b -> (

let h0 = (FStar_HST.get ())
in (

let two52m38 = (FStar_UInt64.uint_to_t (Prims.parse_int "0xfffffffffffda"))
in (

let two52m2 = (FStar_UInt64.uint_to_t (Prims.parse_int "0xffffffffffffe"))
in (

let b0 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "0")))
in (FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "0")) (FStar_UInt64.add b0 two52m38));
(

let h1 = (FStar_HST.get ())
in (

let b1 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "1")))
in (FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "1")) (FStar_UInt64.add b1 two52m2));
(

let h2 = (FStar_HST.get ())
in (

let b2 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "2")))
in (FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "2")) (FStar_UInt64.add b2 two52m2));
(

let h3 = (FStar_HST.get ())
in (

let b3 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "3")))
in (FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "3")) (FStar_UInt64.add b3 two52m2));
(

let h4 = (FStar_HST.get ())
in (

let b4 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "4")))
in (FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "4")) (FStar_UInt64.add b4 two52m2));
(

let h5 = (FStar_HST.get ())
in ());
));
));
));
));
)))))


let aux_lemma_2 : Prims.int  ->  Prims.int  ->  Prims.int  ->  Prims.int  ->  Prims.int  ->  Prims.unit = (fun a b c d e -> ())


let modulo_lemma_2 : Prims.int  ->  Prims.pos  ->  Prims.unit = (fun a b -> ())


let aux_lemma_3 : Prims.int  ->  Prims.unit = (Obj.magic ((fun a -> ())))


let add_big_zero_lemma : heap  ->  heap  ->  Curve_Bigint.bigint  ->  Prims.unit = (Obj.magic ((fun h0 h1 b -> ())))


let add_big_zero : Curve_Bigint.bigint  ->  Prims.unit = (fun b -> (

let h0 = (FStar_HST.get ())
in (add_big_zero_core b);
(

let h1 = (FStar_HST.get ())
in ());
))


let normalize : Curve_Bigint.bigint  ->  Prims.unit = (fun b -> (

let two51m1 = (FStar_UInt64.uint_to_t (Prims.parse_int "0x7ffffffffffff"))
in (

let two51m19 = (FStar_UInt64.uint_to_t (Prims.parse_int "0x7ffffffffffed"))
in (

let b4 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "4")))
in (

let b3 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "3")))
in (

let b2 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "2")))
in (

let b1 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "1")))
in (

let b0 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "0")))
in (

let mask = (FStar_UInt64.eq_mask b4 two51m1)
in (

let mask = (FStar_UInt64.logand mask (FStar_UInt64.eq_mask b3 two51m1))
in (

let mask = (FStar_UInt64.logand mask (FStar_UInt64.eq_mask b2 two51m1))
in (

let mask = (FStar_UInt64.logand mask (FStar_UInt64.eq_mask b1 two51m1))
in (

let mask = (FStar_UInt64.logand mask (FStar_UInt64.gte_mask b0 two51m19))
in (

let sub_mask = (FStar_UInt64.logand mask two51m1)
in (

let sub_mask2 = (FStar_UInt64.logand mask two51m19)
in (

let b4 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "4")))
in (FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "4")) (FStar_UInt64.sub b4 sub_mask));
(

let b3 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "3")))
in (FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "3")) (FStar_UInt64.sub b3 sub_mask));
(

let b2 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "2")))
in (FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "2")) (FStar_UInt64.sub b2 sub_mask));
(

let b1 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "1")))
in (FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "1")) (FStar_UInt64.sub b1 sub_mask));
(

let b0 = (FStar_Buffer.index b (FStar_UInt32.uint_to_t (Prims.parse_int "0")))
in (FStar_Buffer.upd b (FStar_UInt32.uint_to_t (Prims.parse_int "0")) (FStar_UInt64.sub b0 sub_mask2)));
);
);
);
))))))))))))))))


let sum_satisfies_constraints : heap  ->  heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (Obj.magic ((fun h0 h1 cpy a b -> ())))


let mul_satisfies_constraints : heap  ->  heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (Obj.magic ((fun h0 h1 cpy a b -> ())))


let difference_satisfies_constraints : heap  ->  heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Prims.unit = (fun h0 h1 cpy a b -> ())





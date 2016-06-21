
open Prims

let w : FStar_Buffer.u32  ->  Prims.int = FStar_UInt32.v


let vv : Curve_Bigint.u128  ->  Prims.int = FStar_UInt128.v


let op_Plus_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.add


let op_Subtraction_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.sub


type heap =
FStar_HyperStack.mem

type point =
| Point of Curve_Bigint.bigint * Curve_Bigint.bigint * Curve_Bigint.bigint


let ___Point___x : point  ->  Curve_Bigint.bigint = (fun projectee -> (match ((Obj.magic (projectee))) with
| Point (x, y, z) -> begin
x
end))


let ___Point___y : point  ->  Curve_Bigint.bigint = (fun projectee -> (match ((Obj.magic (projectee))) with
| Point (x, y, z) -> begin
y
end))


let ___Point___z : point  ->  Curve_Bigint.bigint = (fun projectee -> (match ((Obj.magic (projectee))) with
| Point (x, y, z) -> begin
z
end))


let get_x : point  ->  Curve_Bigint.bigint = (fun p -> (___Point___x p))


let get_y : point  ->  Curve_Bigint.bigint = (fun p -> (___Point___y p))


let get_z : point  ->  Curve_Bigint.bigint = (fun p -> (___Point___z p))


type 'Ap separateCoordinates =
(((Curve_Bigint.u64, Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.disjoint, (Curve_Bigint.u64, Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.disjoint) Prims.l_and, (Curve_Bigint.u64, Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.disjoint) Prims.l_and


type ('Ah, 'Ap) live =
((((Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.live, (Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.live) Prims.l_and, (Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.live) Prims.l_and, Prims.unit separateCoordinates) Prims.l_and


type ('Ah, 'Ap) wellFormed =
((((Prims.unit, Prims.unit) Curve_Bigint.norm, (Prims.unit, Prims.unit) Curve_Bigint.norm) Prims.l_and, (Prims.unit, Prims.unit) Curve_Bigint.norm) Prims.l_and, Prims.unit separateCoordinates) Prims.l_and


let to_apoint : heap  ->  point  ->  Math_Curve.affine_point = (fun h p -> (Obj.magic (())))


type ('Ah, 'Ap) onCurve =
((Prims.unit, Prims.unit) wellFormed, Prims.unit Math_Curve.curvePoint) Prims.l_and


let refs : point  ->  FStar_Buffer.abuffer FStar_Set.set = (fun p -> (FStar_Buffer.op_Plus_Plus (FStar_Buffer.op_Plus_Plus (FStar_Buffer.only (get_x p)) (get_y p)) (get_z p)))


let erefs : point  ->  FStar_Buffer.abuffer FStar_Set.set FStar_Ghost.erased = (Obj.magic ((fun p -> (Obj.magic (())))))


let op_Plus_Plus_Plus = (fun a b -> (FStar_Set.union a b))


type ('Aa, 'Ab) distinct =
(((((((((Curve_Bigint.u64, Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.disjoint, (Curve_Bigint.u64, Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.disjoint) Prims.l_and, (Curve_Bigint.u64, Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.disjoint) Prims.l_and, (Curve_Bigint.u64, Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.disjoint) Prims.l_and, (Curve_Bigint.u64, Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.disjoint) Prims.l_and, (Curve_Bigint.u64, Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.disjoint) Prims.l_and, (Curve_Bigint.u64, Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.disjoint) Prims.l_and, (Curve_Bigint.u64, Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.disjoint) Prims.l_and, (Curve_Bigint.u64, Curve_Bigint.u64, Prims.unit, Prims.unit) FStar_Buffer.disjoint) Prims.l_and


let set_intersect_lemma = (fun x y -> ())


let make : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  point = (fun x y z -> Point (x, y, z))


let pointOf : heap  ->  point  ->  Math_Curve.celem = (fun h p -> (Obj.magic (())))


type ('Ah0, 'Ah1, 'Ais_swap, 'Actr, 'Aa, 'Ab) partialSwap =
(((((Prims.unit, Prims.unit) Curve_Bigint.norm, (Prims.unit, Prims.unit) Curve_Bigint.norm) Prims.l_and, (Prims.unit, Prims.unit) Curve_Bigint.norm) Prims.l_and, (Prims.unit, Prims.unit) Curve_Bigint.norm) Prims.l_and, Prims.unit) Prims.l_and


let rec swap_conditional_aux' : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Curve_Bigint.u64  ->  FStar_Buffer.u32  ->  Prims.unit = (fun a b swap ctr -> (

let h0 = (FStar_HST.get ())
in (match ((FStar_UInt32.eq Curve_Parameters.nlength ctr)) with
| true -> begin
()
end
| uu____2747 -> begin
(

let ai = (FStar_Buffer.index a ctr)
in (

let bi = (FStar_Buffer.index b ctr)
in (

let y = (FStar_UInt64.op_Hat_Hat ai bi)
in (

let x = (FStar_UInt64.op_Amp_Hat swap y)
in (

let ai' = (FStar_UInt64.op_Hat_Hat x ai)
in (

let bi' = (FStar_UInt64.op_Hat_Hat x bi)
in (FStar_Buffer.upd a ctr ai');
(

let h2 = (FStar_HST.get ())
in (FStar_Buffer.upd b ctr bi');
(

let h3 = (FStar_HST.get ())
in (swap_conditional_aux' a b swap (op_Plus_Bar ctr (FStar_UInt32.uint_to_t (Prims.parse_int "1"))));
(

let h1 = (FStar_HST.get ())
in ());
);
);
))))))
end)))


let rec swap_conditional_aux_lemma : heap  ->  heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Curve_Bigint.u64  ->  Prims.unit = (fun h0 h1 a b swap -> ())


let rec swap_conditional_aux : Curve_Bigint.bigint  ->  Curve_Bigint.bigint  ->  Curve_Bigint.u64  ->  Prims.nat  ->  Prims.unit = (fun a b swap ctr -> (

let h0 = (FStar_HST.get ())
in (swap_conditional_aux' a b swap (FStar_UInt32.uint_to_t (Prims.parse_int "0")));
(

let h1 = (FStar_HST.get ())
in ());
))


let swap_is_on_curve : heap  ->  heap  ->  point  ->  point  ->  Curve_Bigint.u64  ->  Prims.unit = (fun h0 h3 a b is_swap -> ())


let swap_conditional_lemma : heap  ->  heap  ->  heap  ->  heap  ->  point  ->  point  ->  Curve_Bigint.u64  ->  Prims.unit = (fun h0 h1 h2 h3 a b is_swap -> ())


let swap_conditional : point  ->  point  ->  Curve_Bigint.u64  ->  Prims.unit = (fun a b is_swap -> (

let h0 = (FStar_HST.get ())
in (swap_conditional_aux (get_x a) (get_x b) is_swap (Prims.parse_int "0"));
(

let h1 = (FStar_HST.get ())
in (swap_conditional_aux (get_y a) (get_y b) is_swap (Prims.parse_int "0"));
(

let h2 = (FStar_HST.get ())
in (swap_conditional_aux (get_z a) (get_z b) is_swap (Prims.parse_int "0"));
(

let h3 = (FStar_HST.get ())
in ());
);
);
))


let copy : point  ->  point  ->  Prims.unit = (fun a b -> (

let h0 = (FStar_HST.get ())
in (FStar_Buffer.blit (get_x b) (FStar_UInt32.uint_to_t (Prims.parse_int "0")) (get_x a) (FStar_UInt32.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength);
(

let h1 = (FStar_HST.get ())
in (FStar_Buffer.blit (get_y b) (FStar_UInt32.uint_to_t (Prims.parse_int "0")) (get_y a) (FStar_UInt32.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength);
(

let h2 = (FStar_HST.get ())
in (FStar_Buffer.blit (get_z b) (FStar_UInt32.uint_to_t (Prims.parse_int "0")) (get_z a) (FStar_UInt32.uint_to_t (Prims.parse_int "0")) Curve_Parameters.nlength);
(

let h3 = (FStar_HST.get ())
in ());
);
);
))


let swap : point  ->  point  ->  Prims.unit = (fun a b -> (copy b a))


let on_curve_lemma : heap  ->  heap  ->  point  ->  FStar_Buffer.abuffer FStar_Set.set FStar_Ghost.erased  ->  Prims.unit = (Obj.magic ((fun h0 h1 a mods -> ())))


let distinct_lemma : point  ->  point  ->  Prims.unit = (fun a b -> ())


let distinct_commutative : point  ->  point  ->  Prims.unit = (fun a b -> ())


let swap_both : point  ->  point  ->  point  ->  point  ->  Prims.unit = (fun a b c d -> (

let h0 = (FStar_HST.get ())
in (copy c a);
(

let h1 = (FStar_HST.get ())
in (

let set01 = (Obj.magic (()))
in (copy d b);
(

let h2 = (FStar_HST.get ())
in ());
));
))


let copy2 : point  ->  point  ->  point  ->  point  ->  Prims.unit = (fun p' q' p q -> (

let h0 = (FStar_HST.get ())
in (copy p' p);
(

let h1 = (FStar_HST.get ())
in (

let set01 = (Obj.magic (()))
in (copy q' q);
(

let h2 = (FStar_HST.get ())
in ());
));
))





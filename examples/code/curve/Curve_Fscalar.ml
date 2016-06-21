
open Prims

let w : FStar_Buffer.u32  ->  Prims.int = FStar_UInt32.v


let vv : Curve_Bigint.u128  ->  Prims.int = FStar_UInt128.v


let op_Plus_Bar : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.add


let op_Plus_Subtraction : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = FStar_UInt32.sub


type ('Ah, 'Aa, 'As, 'Actr) willNotOverflow =
Prims.unit


type ('Ah0, 'Ah1, 'Actr, 'Alen, 'Aa, 'As, 'Ares) isScalarProduct =
Prims.unit


type ('Ah0, 'Ah1, 'Ares, 'Actr) isNotModified =
Prims.unit


let scalar_multiplication_lemma_aux : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint_wide  ->  Prims.int  ->  Prims.pos  ->  Prims.unit = (Obj.magic ((fun h0 h1 a b s len -> ())))


let rec scalar_multiplication_lemma : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.bigint_wide  ->  Prims.int  ->  Prims.nat  ->  Prims.unit = (fun h0 h1 a b s len -> ())


let rec scalar_multiplication_tr_1 : Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint  ->  Curve_Bigint.u64  ->  FStar_Buffer.u32  ->  Prims.unit = (fun res a s ctr -> (

let ai = (FStar_Buffer.index a ctr)
in (

let z = (FStar_UInt128.mul_wide ai s)
in (FStar_Buffer.upd res ctr z))))


let scalar_multiplication_tr_2 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint  ->  Curve_Bigint.u64  ->  Prims.nat  ->  Prims.unit = (fun h0 h1 h2 res a s ctr -> ())


let rec scalar_multiplication_tr : Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint  ->  Curve_Bigint.u64  ->  FStar_Buffer.u32  ->  Prims.unit = (fun res a s ctr -> (

let h0 = (FStar_HST.get ())
in (match ((FStar_UInt32.eq ctr Curve_Parameters.nlength)) with
| true -> begin
()
end
| uu____1182 -> begin
(

let i = ctr
in (scalar_multiplication_tr_1 res a s ctr);
(

let h1 = (FStar_HST.get ())
in (scalar_multiplication_tr res a s (op_Plus_Bar ctr (FStar_UInt32.uint_to_t (Prims.parse_int "1"))));
(

let h2 = (FStar_HST.get ())
in ());
);
)
end)))


let theorem_scalar_multiplication : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.u64  ->  Prims.nat  ->  Curve_Bigint.bigint_wide  ->  Prims.unit = (fun h0 h1 a s len b -> ())


let auxiliary_lemma_2 : Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.u64  ->  Prims.nat  ->  Prims.unit = (fun ha a s i -> ())


let auxiliary_lemma_0 : Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Curve_Bigint.u64  ->  Prims.unit = (fun ha a s -> ())


let auxiliary_lemma_1 : Curve_Bigint.heap  ->  Curve_Bigint.heap  ->  Curve_Bigint.bigint  ->  Prims.unit  ->  Obj.t FStar_Buffer.buffer  ->  Prims.unit = (fun h0 h1 b t b' -> ())


let scalar' : Curve_Bigint.bigint_wide  ->  Curve_Bigint.bigint  ->  Curve_Bigint.u64  ->  Prims.unit = (fun res a s -> (

let h0 = (FStar_HST.get ())
in (scalar_multiplication_tr res a s (FStar_UInt32.uint_to_t (Prims.parse_int "0")));
(

let h1 = (FStar_HST.get ())
in ());
))





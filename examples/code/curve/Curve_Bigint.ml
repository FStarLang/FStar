
open Prims

type u8 =
FStar_UInt8.t


type u64 =
FStar_UInt64.t


type u128 =
FStar_UInt128.t


type heap =
FStar_HyperStack.mem


type template =
Prims.nat  ->  Prims.pos


type template_const =
template


let byte_templ : Prims.nat  ->  Prims.pos = (fun x -> (Prims.parse_int "8"))


type bigint =
u64 FStar_Buffer.buffer


type bigint_wide =
u128 FStar_Buffer.buffer


type bytes =
u8 FStar_Buffer.buffer


type ('Ah, 'Ab) norm =
(((u64, Prims.unit, Prims.unit) FStar_Buffer.live, Prims.unit Prims.b2t) Prims.l_and, Prims.unit) Prims.l_and


type ('Ah, 'Ab) norm_wide =
(((u128, Prims.unit, Prims.unit) FStar_Buffer.live, Prims.unit Prims.b2t) Prims.l_and, Prims.unit) Prims.l_and


type ('Ah, 'Ab) null =
((u64, Prims.unit, Prims.unit) FStar_Buffer.live, Prims.unit) Prims.l_and


type ('Ah, 'Ab) null_wide =
((u128, Prims.unit, Prims.unit) FStar_Buffer.live, Prims.unit) Prims.l_and


type ('Ah, 'Ab) filled =
(((u64, Prims.unit, Prims.unit) FStar_Buffer.live, Prims.unit Prims.b2t) Prims.l_and, Prims.unit) Prims.l_and


let rec bitweight : template  ->  Prims.nat  ->  Prims.nat = (fun t n -> (Obj.magic (())))


let bitweight_def : template  ->  Prims.int  ->  Prims.unit = (fun t n -> ())


let rec eval : heap  ->  bigint  ->  Prims.nat  ->  Prims.nat = (fun h b n -> (Obj.magic (())))


let rec eval_wide : heap  ->  bigint_wide  ->  Prims.nat  ->  Prims.nat = (fun h b n -> (Obj.magic (())))


let eval_def : FStar_HyperStack.mem  ->  bigint  ->  Prims.nat  ->  Prims.unit = (fun h b n -> ())


let eval_wide_def : FStar_HyperStack.mem  ->  bigint_wide  ->  Prims.nat  ->  Prims.unit = (fun h b n -> ())


let rec eval_bytes : heap  ->  bytes  ->  Prims.nat  ->  Prims.nat = (fun h b n -> (Obj.magic (())))


let rec maxValue : heap  ->  bigint  ->  Prims.pos  ->  Prims.nat = (fun h b l -> (Obj.magic (())))


let rec maxValue_wide : heap  ->  bigint_wide  ->  Prims.pos  ->  Prims.nat = (fun h b l -> (Obj.magic (())))


let rec maxValue_lemma_aux : heap  ->  bigint  ->  Prims.pos  ->  Prims.unit = (fun h b l -> ())


let rec maxValue_lemma : heap  ->  bigint  ->  Prims.unit = (Obj.magic ((fun h b -> ())))


let rec maxValue_bound_lemma_aux : heap  ->  bigint  ->  Prims.pos  ->  Prims.nat  ->  Prims.unit = (fun h b l bound -> ())


let maxValue_bound_lemma : heap  ->  bigint  ->  Prims.nat  ->  Prims.unit = (Obj.magic ((fun h b bound -> ())))


let maxValueNorm : heap  ->  bigint  ->  Prims.nat = (fun h b -> (Obj.magic (())))


let rec maxValueIdx : heap  ->  bigint  ->  Prims.pos  ->  Prims.nat = (fun h b l -> (Obj.magic (())))


let rec maxValue_eq_lemma : heap  ->  heap  ->  bigint  ->  bigint  ->  Prims.pos  ->  Prims.unit = (fun ha hb a b l -> ())


let maxValueNorm_eq_lemma : heap  ->  heap  ->  bigint  ->  bigint  ->  Prims.unit = (fun ha hb a b -> ())


let rec eval_eq_lemma : heap  ->  heap  ->  bigint  ->  bigint  ->  Prims.nat  ->  Prims.unit = (fun ha hb a b len -> ())


let rec eval_partial_eq_lemma : heap  ->  heap  ->  bigint  ->  bigint  ->  Prims.nat  ->  Prims.nat  ->  Prims.unit = (fun ha hb a b ctr len -> ())


let rec eval_null : heap  ->  bigint  ->  Prims.nat  ->  Prims.unit = (fun h b len -> ())


let rec max_value_of_null_lemma : heap  ->  bigint  ->  Prims.pos  ->  Prims.unit = (fun h b l -> ())





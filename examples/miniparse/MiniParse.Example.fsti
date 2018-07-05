(* NOTE: This example MUST BE in an .fsti because of --use_extracted_interfaces *)

module MiniParse.Example
include MiniParse.Spec.TEnum
include MiniParse.Tac.Impl

module T = FStar.Tactics
module U8 = FStar.UInt8

type test = | TA | TB | TC | TD

#set-options "--no_smt"

let f : test -> Tot U8.t = T.synth_by_tactic (fun () -> gen_synth (`(test)))

let g : U8.t -> Tot test = T.synth_by_tactic (fun () -> invert_function (`(test)) (`(U8.t)) (`(op_Equality #U8.t)) (`(f)))

let test_bound : nat = T.synth_by_tactic (fun () -> tenum_bound (`(test)))

let f' : test -> Tot (bounded_u8 test_bound) = T.synth_by_tactic (fun () -> gen_synth_bounded (`(test)))

let g' : bounded_u8 test_bound -> Tot test = T.synth_by_tactic (fun () -> invert_function  (`(test)) (`(bounded_u8 test_bound)) (`(op_Equality #(bounded_u8 test_bound))) (`(f')))

let g'_injective: squash (synth_injective g') =
  T.synth_by_tactic (fun () -> synth_injective_solve (`f'))

let g'_inverse: squash (synth_inverse g' f') =
  T.synth_by_tactic synth_inverse_solve

let p : parser test = T.synth_by_tactic (fun () -> gen_enum_parser (`test))

(*
let q : parser32 p = T.synth_by_tactic (fun () -> gen_parser32 (`p))
*)

#reset-options

// At this point, SMT is back on

#set-options "--z3rlimit 32"

let q' : parser32 p =
  MiniParse.Impl.Combinators.parse32_synth (MiniParse.Spec.TEnum.parse_bounded_u8 4)
  (fun x2 ->
       MiniParse.Tac.Base.mk_if_t (MiniParse.Spec.TEnum.bounded_u8_eq 4
             x2
             (MiniParse.Spec.TEnum.mk_u8 0))
         (fun _ -> TA)
         (fun _ ->
             MiniParse.Tac.Base.mk_if_t (MiniParse.Spec.TEnum.bounded_u8_eq 4
                   x2
                   (MiniParse.Spec.TEnum.mk_u8 1))
               (fun _ -> TB)
               (fun _ ->
                   MiniParse.Tac.Base.mk_if_t (MiniParse.Spec.TEnum.bounded_u8_eq 4
                         x2
                         (MiniParse.Spec.TEnum.mk_u8 2))
                     (fun _ -> TC)
                     (fun _ -> TD))))
   (fun x0 ->
       (fun x2 ->
           MiniParse.Tac.Base.mk_if_t (MiniParse.Spec.TEnum.bounded_u8_eq 4
                 x2
                 (MiniParse.Spec.TEnum.mk_u8 0))
             (fun _ -> TA)
             (fun _ ->
                 MiniParse.Tac.Base.mk_if_t (MiniParse.Spec.TEnum.bounded_u8_eq 4
                       x2
                       (MiniParse.Spec.TEnum.mk_u8 1))
                   (fun _ -> TB)
                   (fun _ ->
                       MiniParse.Tac.Base.mk_if_t (MiniParse.Spec.TEnum.bounded_u8_eq 4
                             x2
                             (MiniParse.Spec.TEnum.mk_u8 2))
                         (fun _ -> TC)
                         (fun _ -> TD)))) x0)
   (MiniParse.Impl.Combinators.parse32_synth (MiniParse.Spec.Combinators.parse_filter MiniParse.Spec.Int.parse_u8
           (fun x -> FStar.UInt8.v x < 4))
       (fun x -> x <: MiniParse.Spec.TEnum.bounded_u8 4)
       (fun x1 -> (fun x -> x <: MiniParse.Spec.TEnum.bounded_u8 4) x1)
       (MiniParse.Impl.Combinators.parse32_filter MiniParse.Impl.Int.parse32_u8
           (fun x -> FStar.UInt8.v x < 4)
           (fun x2 -> (fun x -> FStar.UInt8.v x < 4) x2))
       ())
   ()

module MiniParseExample
open MiniParse.Spec.TEnum
open MiniParse.Tac.Impl
open MiniParse.Spec.TSum

module T = FStar.Tactics
module U8 = FStar.UInt8

#set-options "--no_smt"

(*
let f : test -> Tot U8.t = T.synth_by_tactic (fun () -> gen_synth (`(test)))

let g : U8.t -> Tot test = T.synth_by_tactic (fun () -> invert_function (`(test)) (`(U8.t)) (`(op_Equality #U8.t)) (`(f)))

let test_bound : nat = T.synth_by_tactic (fun () -> tenum_bound (`(test)))

let f' : test -> Tot (bounded_u8 test_bound) = T.synth_by_tactic (fun () -> gen_synth_bounded (`(test)))

let g' : bounded_u8 test_bound -> Tot test = T.synth_by_tactic (fun () -> invert_function  (`(test)) (`(bounded_u8 test_bound)) (`(op_Equality #(bounded_u8 test_bound))) (`(f')))

let g'_inverse: squash (synth_inverse g' f') =
  T.synth_by_tactic synth_inverse_forall_tenum_solve

let g'_injective: squash (synth_inverse f' g') =
  T.synth_by_tactic synth_inverse_forall_bounded_u8_solve
*)

let p = T.synth_by_tactic (fun () -> gen_enum_parser (`test))

let q = T.synth_by_tactic (fun () -> gen_parser32 (`p))

#reset-options

let bidon = ()

let j (x: nat) : Tot unit = assert (x > 2 ==> x + x > 4)

#set-options "--z3rlimit 32"

let somme_p' : unit =
(
  [@inline_let]
  let imp0 =
    (fun (x: somme) -> match x with
    | U _ -> 0uy <: bounded_u8 4
    | V -> 1uy <: bounded_u8 4
    | W -> 2uy <: bounded_u8 4
    | _ -> 3uy <: bounded_u8 4)
  in
  [@inline_let]
  let imp1 =
    (bounded_u8_match_t_intro 4 (fun _ -> Type0) (
      bounded_u8_match_t_aux_cons 4 _ 3 Type0 () unit (
      bounded_u8_match_t_aux_cons 4 _ 2 Type0 () unit (
      bounded_u8_match_t_aux_cons 4 _ 1 Type0 () unit (
      bounded_u8_match_t_aux_cons_nil 4 _ Type0 () U8.t
    )))))  
  in
  [@inline_let]
  let imp2 = (fun (x: bounded_u8 4) -> parser (imp1 x)) in
  [@inline_let]
  let imp3 =
    bounded_u8_match_t_intro 4 imp2 (
      bounded_u8_match_t_aux_cons 4 imp2 3 (parser unit) () parse_empty (
      bounded_u8_match_t_aux_cons 4 imp2 2 (parser unit) () parse_empty (
      bounded_u8_match_t_aux_cons 4 imp2 1 (parser unit) () parse_empty (
      bounded_u8_match_t_aux_cons_nil 4 imp2 (parser U8.t) () parse_u8
    ))))
  in
  ()
) <: unit by (fun () -> let open FStar.Tactics in
    set_guard_policy Goal;
    fail "here"
)

(*
fail "here")

(*
  parse_sum
    (parse_bounded_u8 4)
    imp0
    #imp1
    imp2
    (fun (x: bounded_u8 4) y -> bounded_u8_match_t_intro 4 (refine_with_tag imp0) (
      bounded_u8_match_t_aux_cons 4 _ 3 X (
      bounded_u8_match_t_aux_cons 4 _ 2 W (
      bounded_u8_match_t_aux_cons 4 _ 1 V (
      bounded_u8_match_t_aux_cons 4 _ 0 (U y)
    )))))

    
    (fun (x: bounded_u8 4) y -> bounded_u8_match_t_intro 4 _ (
      bounded_u8_match_t_aux_cons 4 _ 3 () (
      bounded_u8_match_t_aux_cons 4 _ 2 () (
      bounded_u8_match_t_aux_cons 4 _ 1 () (
      bounded_u8_match_t_aux_cons 4 _ 0 (let (U y) = y in y)
    )))))

    (fun x y -> match x with
    | TA -> U y <: refine_with_tag tod x
    | TB -> V <: refine_with_tag tod x
    | TC -> W <: refine_with_tag tod x
    | TD -> X <: refine_with_tag tod x)
    (fun x y -> match x with
    | TB -> () <: ty x
    | TA -> let (U v) = y in v <: ty x
    | TC -> () <: ty x
    | TD -> () <: ty x)

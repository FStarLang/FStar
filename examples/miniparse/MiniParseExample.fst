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

let somme_p =
  [@inline_let]
  let tod (x: somme) : Tot test = match x with
  | U _ -> TA | V -> TB | W -> TC | _ -> TD
  in
  [@inline_let]
  let ty (x: test) : Tot Type0 = match x with
  | TA -> U8.t | _ -> unit
  in
  [@inline_let]
  let ps (x: test) : Tot (parser (ty x)) = match x with
  | TA -> parse_u8 <: parser (ty x) | TB -> parse_empty <: parser (ty x) | TC -> parse_empty <: parser (ty x) | TD -> parse_empty <: parser (ty x)
  in
  parse_sum
    p
    tod
    #ty
    ps
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

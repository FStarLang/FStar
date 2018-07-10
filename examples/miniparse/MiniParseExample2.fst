module MiniParseExample2
open MiniParse.Spec.TSum

module T = FStar.Tactics
module U8 = FStar.UInt8

noeq
type somme = | U of FStar.UInt8.t | V | W | X

#set-options "--z3rlimit 16"

  let imp0 (x: somme) : Tot (bounded_u8 4) = match x with
    | U _ -> 0uy <: bounded_u8 4
    | V -> 1uy <: bounded_u8 4
    | W -> 2uy <: bounded_u8 4
    | _ -> 3uy <: bounded_u8 4

#set-options "--print_universes --print_implicits"

let c3 : sum_case #somme #(bounded_u8 4) imp0 3uy =
  Case #(bounded_u8 4) #somme
        unit
        parse_empty
        serialize_empty
        (fun (_: unit) -> X <: refine_with_tag #(bounded_u8 4) #somme imp0 (3uy <: bounded_u8 4))
        (fun (_: refine_with_tag #(bounded_u8 4) #somme imp0 (3uy <: bounded_u8 4)) -> ())
        ()

#set-options "--z3rlimit 64"

let c2 : sum_case #somme #(bounded_u8 4) imp0 2uy =
  Case #(bounded_u8 4) #somme
        unit
        parse_empty
        serialize_empty
        (fun (_: unit) -> W <: refine_with_tag #(bounded_u8 4) #somme imp0 (2uy <: bounded_u8 4))
        (fun (x: refine_with_tag #(bounded_u8 4) #somme imp0 (2uy <: bounded_u8 4)) -> ())
        ()

let c1 : sum_case #somme #(bounded_u8 4) imp0 1uy =
  Case #(bounded_u8 4) #somme
        unit
        parse_empty
        serialize_empty
        (fun (_: unit) -> V <: refine_with_tag #(bounded_u8 4) #somme imp0 (1uy <: bounded_u8 4))
        (fun (_: refine_with_tag #(bounded_u8 4) #somme imp0 (1uy <: bounded_u8 4)) -> ())
        ()

let c0 : sum_case #somme #(bounded_u8 4) imp0 0uy =
  Case #(bounded_u8 4) #somme
        U8.t
        parse_u8
        serialize_u8
        (fun (x: U8.t) -> U x <: refine_with_tag #(bounded_u8 4) #somme imp0 (0uy <: bounded_u8 4))
        (fun (x: refine_with_tag #(bounded_u8 4) #somme imp0 0uy) -> (
          match x with 
          | U x -> x
        ))
        ()

#reset-options

let imp1 : (x: bounded_u8 4) -> Tot (sum_case #somme #(bounded_u8 4) imp0 x) =
    (bounded_u8_match_t_intro 4 imp0 (
      bounded_u8_match_t_aux_cons 4 imp0 3 3uy (
        c3
      ) (
      bounded_u8_match_t_aux_cons 4 imp0 2 2uy (
        c2
      ) (
      bounded_u8_match_t_aux_cons 4 imp0 1 1uy (
        c1
      ) (
      bounded_u8_match_t_aux_cons_nil 4 imp0 (
        c0
      ))))))

noextract
val somme_p : parser somme

let somme_p =
  parse_sum
    (parse_bounded_u8 4)
    imp0
    imp1

// val somme_p32: parser32 somme_p

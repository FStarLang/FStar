(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module MiniParseExample2
open MiniParse.Spec.TSum

module T = FStar.Tactics
module U8 = FStar.UInt8

noeq
type somme = | U of FStar.UInt8.t | V | W | X

#set-options "--z3rlimit 16"

  let imp0 (x: somme) : Tot (bounded_u16 4) = match x with
    | U _ -> 0us <: bounded_u16 4
    | V -> 1us <: bounded_u16 4
    | W -> 2us <: bounded_u16 4
    | _ -> 3us <: bounded_u16 4

#set-options "--print_universes --print_implicits"

let c3 : sum_case #somme #(bounded_u16 4) imp0 3us =
  Case #(bounded_u16 4) #somme
        unit
        parse_empty
        serialize_empty
        (fun (_: unit) -> X <: refine_with_tag #(bounded_u16 4) #somme imp0 (3us <: bounded_u16 4))
        (fun (_: refine_with_tag #(bounded_u16 4) #somme imp0 (3us <: bounded_u16 4)) -> ())
        ()

#set-options "--z3rlimit 64"

let c2 : sum_case #somme #(bounded_u16 4) imp0 2us =
  Case #(bounded_u16 4) #somme
        unit
        parse_empty
        serialize_empty
        (fun (_: unit) -> W <: refine_with_tag #(bounded_u16 4) #somme imp0 (2us <: bounded_u16 4))
        (fun (x: refine_with_tag #(bounded_u16 4) #somme imp0 (2us <: bounded_u16 4)) -> ())
        ()

let c1 : sum_case #somme #(bounded_u16 4) imp0 1us =
  Case #(bounded_u16 4) #somme
        unit
        parse_empty
        serialize_empty
        (fun (_: unit) -> V <: refine_with_tag #(bounded_u16 4) #somme imp0 (1us <: bounded_u16 4))
        (fun (_: refine_with_tag #(bounded_u16 4) #somme imp0 (1us <: bounded_u16 4)) -> ())
        ()

let c0 : sum_case #somme #(bounded_u16 4) imp0 0us =
  Case #(bounded_u16 4) #somme
        U8.t
        parse_u8
        serialize_u8
        (fun (x: U8.t) -> U x <: refine_with_tag #(bounded_u16 4) #somme imp0 (0us <: bounded_u16 4))
        (fun (x: refine_with_tag #(bounded_u16 4) #somme imp0 0us) -> (
          match x with 
          | U x -> x
        ))
        ()

#reset-options

let imp1 : (x: bounded_u16 4) -> Tot (sum_case #somme #(bounded_u16 4) imp0 x) =
    (bounded_u16_match_t_intro 4 imp0 (
      bounded_u16_match_t_aux_cons 4 imp0 3 3us (
        c3
      ) (
      bounded_u16_match_t_aux_cons 4 imp0 2 2us (
        c2
      ) (
      bounded_u16_match_t_aux_cons 4 imp0 1 1us (
        c1
      ) (
      bounded_u16_match_t_aux_cons_nil 4 imp0 (
        c0
      ))))))

noextract
val somme_p : parser_spec somme

let somme_p =
  parse_sum
    (parse_bounded_u16 4)
    imp0
    imp1

// val somme_p32: parser32 somme_p

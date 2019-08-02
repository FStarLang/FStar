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
module IfcDelimitedRelease

open FStar.Heap
open Rel

type label =
| Low
| High

type env = nat ->  GTot label
type iexpr = heap -> GTot int
type bexpr = heap -> GTot bool

let rel_contains (h:rel heap) (r:ref int) = (R?.l h) `contains` r /\ (R?.r h) `contains` r

let rec refs_invariant (l:list (ref int)) (h:heap) :Type0 =
  match l with
  | []   -> True
  | r::tl ->
    h `contains` r /\
    (forall (r1:ref int). FStar.List.Tot.memP r1 tl ==> addr_of r <> addr_of r1) /\
    refs_invariant tl h

type prog (i:nat) = vl:list(ref int){List.Tot.length vl = i} -> h:heap{refs_invariant vl h} -> GTot heap

type low_equiv (h : rel heap) (env:env) = (forall (x:ref int).
                                             (h `rel_contains` x /\ Low? (env (addr_of x))) ==> sel (R?.l h) x = sel (R?.r h) x)

val iexpr_eq : rel heap -> iexpr -> GTot bool
let iexpr_eq (R hl hr) e = e hl = e hr

val bexpr_eq : rel heap -> bexpr -> GTot bool
let bexpr_eq (R hl hr) e = e hl = e hr

val g_for_all: ('a -> GTot bool) -> list 'a -> GTot bool
let rec g_for_all f l = match l with
    | [] -> true
    | hd::tl -> if f hd then g_for_all f tl else false
type del_rel (i:int) (env:env) (vl : list (ref int){List.Tot.length vl = i}) (ihel : list iexpr) (bhel : list bexpr) (c:prog i) =
  forall h.
    (refs_invariant vl (R?.l h) /\
     refs_invariant vl (R?.r h) /\
     low_equiv h env /\
     g_for_all (iexpr_eq h) ihel /\
     g_for_all (bexpr_eq h) bhel)
      ==> low_equiv (R (c vl (R?.l h)) (c vl (R?.r h))) env

val test : prog 3
let test [x;y;z] h =
  let tmp1 = sel h y in
  let tmp2 = sel h z in
  upd h x (tmp1 + tmp2)

private val verify_test (x y z: ref int):
  Lemma begin
    let n = 3 in
    let l = [x ; y ; z] in
    let y_add = addr_of y in
    let z_add = addr_of z in
    let env (r: nat) =  //AR: in the extracted interface, y_add and z_add are inlined in the following,
                 //    which means the effect is now GTot, so i had to make env as ref int -> GTot label
      if r = y_add || r = z_add then High
      else Low
    in
    let res h = sel h y + sel h z in
    del_rel n env l [res] [] test
  end
let verify_test x y z = Heap.lemma_distinct_addrs_distinct_preorders (); Heap.lemma_distinct_addrs_distinct_mm ()


val sum : prog 6

let sum [x1;x2;x3;x4;x5;y] h =
  upd h y ((sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5))

private val verify_sum (x1 x2 x3 x4 x5 y : ref int):
  Lemma
    (let y_add = addr_of y in
     let l = [addr_of x1; addr_of x2; addr_of x3; addr_of x4; addr_of x5] in
      (del_rel 6
      (fun r ->
        if r = y_add then Low
        else if List.Tot.mem r l then High
        else Low)
      [x1;x2;x3;x4;x5;y]
      [fun h -> sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5]
      []
      sum))
let verify_sum x1 x2 x3 x4 x5 y = Heap.lemma_distinct_addrs_distinct_preorders (); Heap.lemma_distinct_addrs_distinct_mm ()

val sum_swap : prog 6
let sum_swap l h =
  let [x1; x2; x3; x4; x5; y] = l in
  let tmp1 = sel h x1 in
  let h = upd h x1 (sel h x2) in
  let h = upd h x2 (sel h x3) in
  let h = upd h x3 (sel h x4) in
  let h = upd h x4 (sel h x5) in
  let h = upd h x5 tmp1 in
  upd h y ((sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5))

private val verify_sum_swap (x1 x2 x3 x4 x5 y : ref int):
  Lemma
    (let y_add = addr_of y in
     let l = [addr_of x1; addr_of x2; addr_of x3; addr_of x4; addr_of x5] in
      (del_rel 6
      (fun r ->
        if r = y_add then Low
        else if List.Tot.mem r l then High
        else Low)
      [x1;x2;x3;x4;x5;y]
      [fun h -> sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5]
      []
      sum_swap))
#set-options "--z3rlimit 30"
let verify_sum_swap x1 x2 x3 x4 x5 y = Heap.lemma_distinct_addrs_distinct_preorders (); Heap.lemma_distinct_addrs_distinct_mm ()



val sum_att : prog 6
let sum_att [x1;x2;x3;x4;x5;y] h =
  let tmp1 = sel h x1 in
  let h = upd h x2 tmp1 in
  let h = upd h x3 tmp1 in
  let h = upd h x4 tmp1 in
  let h = upd h x5 tmp1 in
  upd h y ((sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5))

(* This does not verify, as expected *)
(*
// val verify_sum_att (x1 x2 x3 x4 x5 y : ref int):
//   Lemma
//     (del_rel 6
//       (fun r ->
//         if r = y then Low
//         else if List.Tot.mem r [x1;x2;x3;x4;x5] then High
//         else Low)
//       [x1;x2;x3;x4;x5;y]
//       [fun h -> sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5]
//       sum_att)
// let verify_sum_att x1 x2 x3 x4 x5 y = ()
// *)


val wallet : prog 3
let wallet [x_h;k;x_l] h =
  if (sel h x_h >= sel h k) then
    let h = upd h x_h (sel h x_h - sel h k) in
    let h = upd h x_l (sel h x_l + sel h k) in
    h
  else
    h

private val verify_wallet (x_h k x_l : ref int):
  Lemma
    (let x_h_addr = addr_of x_h in
     (del_rel 3
      (fun r ->
        if r = x_h_addr then High
        else Low)
      [x_h; k; x_l]
      []
      [fun h -> sel h x_h >= sel h k]
      wallet))
let verify_wallet x_h k x_l = Heap.lemma_distinct_addrs_distinct_preorders (); Heap.lemma_distinct_addrs_distinct_mm ()

// This is not accepted
//val wallet_attack_loop : prog 4
val wallet_attack_loop : vl:list(ref int){List.Tot.length vl = 4} -> h:heap{refs_invariant vl h} -> GTot heap (decreases (sel h (List.Tot.hd vl)))
let rec wallet_attack_loop [n;x_h;k;x_l] h =
  if sel h n <= 0 then
    h
  else
    let h = upd h k (pow2 (sel h n - 1)) in
    let h = wallet [x_h;k;x_l] h in
    let h = upd h n (sel h n - 1) in
    wallet_attack_loop [n;x_h;k;x_l] h

val wallet_attack : prog 4
let wallet_attack [n;x_h;k;x_l] h =
 let h = upd h x_l 0 in
 wallet_attack_loop [n;x_h;k;x_l] h

(* This does not verify, as expected
//    Howver, also does not verify wieht x_h : Low, which should be fine *)
(*
// val verify_wallet_attack (n x_h k x_l : ref int):
//   Lemma
//     (del_rel 4
//       (fun r ->
//         if r = x_h then High
//         else Low)
//       [n; x_h; k; x_l]
//       []
//       [fun h -> sel h x_h >= sel h k]
//       wallet_attack)
// let verify_wallet_attack n x_h k x_l = ()
// *)

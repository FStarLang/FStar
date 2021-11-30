(*
   Copyright 2021 Microsoft Research

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
module Steel.ST.Loops
module U32 = FStar.UInt32
open Steel.ST.Util
open Steel.ST.Coercions
module L = Steel.Loops
module SE = Steel.Effect
module SEA = Steel.Effect.Atomic
open FStar.Ghost

(* This module provides some common iterative looping combinators *)

let for_loop' (start:U32.t)
              (finish:U32.t { U32.v start <= U32.v finish })
              (inv: nat_at_most finish -> vprop)
              ($body:
                    (i:u32_between start finish ->
                          STT unit
                          (inv (U32.v i))
                          (fun _ -> inv (U32.v i + 1))))
  : SE.SteelT unit
      (inv (U32.v start))
      (fun _ -> inv (U32.v finish))
  = L.for_loop start finish inv body //lift works for body

let for_loop (start:U32.t)
             (finish:U32.t { U32.v start <= U32.v finish })
             (inv: nat_at_most finish -> vprop)
             (body:
                    (i:u32_between start finish ->
                          STT unit
                          (inv (U32.v i))
                          (fun _ -> inv (U32.v i + 1))))
  : STT unit
      (inv (U32.v start))
      (fun _ -> inv (U32.v finish))
  = coerce_steel (fun _ -> for_loop' start finish inv body); ()

let elim_h_exists (#a:Type) #o (p:a -> vprop)
  : STGhostT (Ghost.erased a) o
            (SEA.h_exists p)
            (fun v -> p v)
  = let x = coerce_ghost SEA.witness_exists in x

let intro_h_exists (#a:Type) #o (v:Ghost.erased a) (p:a -> vprop)
  : STGhostT unit o
            (p v)
            (fun _ -> SEA.h_exists p)
  = let _ = coerce_ghost (fun _ -> SEA.intro_exists_erased v p) in ()

let exists_to_h_exists (#a:Type) #o (p:a -> vprop)
  : STGhostT unit o (exists_ p)
                  (fun _ -> SEA.h_exists p)
  = let w = elim_exists () in
    intro_h_exists w p

let coerce_cond (inv: Ghost.erased bool -> vprop)
                (cond: (unit -> STT bool
                                   (exists_ inv)
                                   (fun b -> inv b)))
                (_:unit)
  : STT bool (SEA.h_exists inv) (fun b -> inv b)
  = let w = elim_h_exists inv in
    intro_exists_erased w inv;
    cond ()

let coerce_body (inv: Ghost.erased bool -> vprop)
                (body: (unit -> STT unit
                                   (inv true)
                                   (fun _ -> exists_ inv)))
                (_:unit)
  : STT unit (inv true) (fun _ -> SEA.h_exists inv)
  = let b = body () in
    let w = elim_exists () in
    intro_h_exists w inv;
    return b

/// while_loop: while (cond()) { body () }
let while_loop' (inv: Ghost.erased bool -> vprop)
                ($cond: (unit -> STT bool
                                     (exists_ inv)
                                     (fun b -> inv b)))
                ($body: (unit -> STT unit
                                     (inv true)
                                     (fun _ -> exists_ inv)))
  : SE.SteelT unit
              (SEA.h_exists inv)
              (fun _ -> inv false)
  = L.while_loop
       inv
       (coerce_cond inv cond)
       (coerce_body inv body)

let exists_to_e_exists (#a:Type) #o (p:a -> vprop)
  : STGhostT unit o (exists_ p)
                    (fun _ -> exists_ (fun (x:erased a) -> p x))
  = let w = elim_exists () in
    intro_exists w (fun (x:erased a) -> p x)

let e_exists_to_exists (#a:Type) #o (p:a -> vprop)
  : STGhostT unit o (exists_ (fun (x:erased a) -> p x))
                    (fun _ -> exists_ p)
  = let w = elim_exists () in
    intro_exists #a (reveal (reveal w)) p

let lift_cond_exists_to_e_exists
                   (inv: bool -> vprop)
                   (cond: (unit -> STT bool
                                     (exists_ inv)
                                     (fun b -> inv b)))
                   (_:unit)
  : STT bool
        (exists_ (fun (b:erased bool) -> inv b))
        (fun b -> inv b)
  = e_exists_to_exists inv;
    let b = cond () in
    b

let lift_body_exists_to_e_exists
                   (inv: bool -> vprop)
                   (body: (unit -> STT unit
                                     (inv true)
                                     (fun _ -> exists_ inv)))
                   (_:unit)
  : STT unit
        (inv true)
        (fun _ -> exists_ (fun (b:erased bool) -> inv b))
  = body ();
    exists_to_e_exists inv


/// while_loop: while (cond()) { body () }
let while_loop (inv: bool -> vprop)
               (cond: (unit -> STT bool
                                  (exists_ inv)
                                  (fun b -> inv b)))
               (body: (unit -> STT unit
                                  (inv true)
                                  (fun _ -> exists_ inv)))
  : STT unit
        (exists_ inv)
        (fun _ -> inv false)
  = let w = elim_exists () in
    intro_exists w (fun (b:erased bool) -> inv b);
    exists_to_h_exists (fun (b:erased bool) -> inv b);
    coerce_steel (fun _ ->
      while_loop'
        (fun b -> inv b)
        (lift_cond_exists_to_e_exists inv cond)
        (lift_body_exists_to_e_exists inv body))

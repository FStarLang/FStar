(*
   Copyright 2020 Microsoft Research

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

module SteelFramingTestSuite

open Steel.Memory
open Steel.Effect

/// A collection of small unit tests for the framing tactic

assume val p : vprop
assume val f (x:int) : SteelT unit p (fun _ -> p)

let test () : SteelT unit (p `star` p `star` p) (fun _ -> p `star` p `star` p)
  = f 0; ()

assume val ref : Type0
assume val ptr (_:ref) : vprop

assume val alloc (x:int)  : SteelT ref emp (fun y -> ptr y)
assume val free (r:ref) : SteelT unit (ptr r) (fun _ -> emp)
assume val read (r:ref) : SteelT int (ptr r) (fun _ -> ptr r)
assume val write (r:ref) (v: int) : SteelT unit (ptr r) (fun _ -> ptr r)

let test0 (b1 b2 b3: ref) : SteelT int
  (ptr b1 `star` ptr b2 `star` ptr b3)
  (fun _ -> ptr b1 `star` ptr b2 `star` ptr b3)
  =
  let x = read b1 in
  x

let test1 (b1 b2 b3: ref) : SteelT int
  (ptr b1 `star` ptr b2 `star` ptr b3)
  (fun _ -> ptr b1 `star` ptr b2 `star` ptr b3)
  =
  let x = (let y = read b1 in y) in
  x

let test2 (b1 b2 b3: ref) : SteelT int
  (ptr b1 `star` ptr b2 `star` ptr b3)
  (fun _ -> ptr b3 `star` ptr b2 `star` ptr b1)
  =
  let x = read b1 in
  x

let test3 (b1 b2 b3: ref) : SteelT int
  (ptr b1 `star` ptr b2 `star` ptr b3)
  (fun _ -> ptr b2 `star` ptr b1 `star` ptr b3)
  =
  let x = read b3 in
  x

let test4 (b1 b2 b3: ref) : SteelT unit
  (ptr b1 `star` ptr b2 `star` ptr b3)
  (fun _ -> ptr b2 `star` ptr b1 `star` ptr b3)
  =
  let x = read b3 in
  write b2 x

let test5 (b1 b2 b3: ref) : SteelT unit
  (ptr b1 `star` ptr b2 `star` ptr b3)
  (fun _ -> ptr b2 `star` ptr b1 `star` ptr b3)
  =
  let x = read b3 in
  write b2 (x + 1)

let test6 (b1 b2 b3: ref) : SteelT unit
  (ptr b1 `star` ptr b2 `star` ptr b3)
  (fun _ -> ptr b2 `star` ptr b1 `star` ptr b3)
  =
  let x = read b3 in
  let b4 = alloc x in
  write b2 (x + 1);
  free b4

// With the formalism relying on can_be_split_post, this example fails if we normalize return_pre eqs goals before unification
// When solving this equality, we have the goal
// (*?u19*) _ _ == return_pre ((fun x -> (fun x -> (*?u758*) _ x x) x) r)
// with x and r in the context of ?u19
// Not normalizing allows us to solve it as a function applied to x and r
// Normalizing would lead to solve it to an slprop with x and r in the context,
// but which would later fail when trying to prove the equivalence with (fun r -> ptr r)
// in the postcondition
let test7 (_:unit) : SteelT ref emp ptr
  = let r = alloc 0 in
    let x = read r in
    write r 0;
    r

let test8 (b1 b2 b3:ref) : SteelT unit
  (ptr b1 `star` ptr b2 `star` ptr b3)
  (fun _ -> ptr b2 `star` ptr b1 `star` ptr b3)
  = write b2 0

open Steel.Effect.Atomic

let test_if1 (b:bool) : SteelT unit emp (fun _ -> emp)
  = if b then noop () else noop ()

let test_if2 (b:bool) (r: ref) : SteelT unit (ptr r) (fun _ -> ptr r)
  = if b then write r 0 else write r 1

let test_if3 (b:bool) (r:ref) : SteelT unit (ptr r) (fun _ -> ptr r)
  = if b then noop () else noop ()

let test_if4 (b:bool) : SteelT unit emp (fun _ -> emp)
  = if b then (let r = alloc 0 in free r) else (noop ())

let test_if5 (b:bool) : SteelT ref emp (fun r -> ptr r)
  = if b then alloc 0 else alloc 1

let test_if6 (b:bool) : SteelT ref emp (fun r -> ptr r)
  = let r = if b then alloc 0 else alloc 1 in
    let x = read r in
    write r 0;
    r

(* First test with different (but equivalent) slprops in both branches *)
let test_if7 (b:bool) (r1 r2: ref) : SteelT unit
  (ptr r1 `star` ptr r2)
  (fun _ -> ptr r1 `star` ptr r2)
  = if b then (write r1 0; write r2 0) else (write r2 0; write r1 0);
    write r2 0

(* Test with different slprops in both branches. The second branch captures the outer frame in its context *)
let test_if8 (b:bool) (r1 r2: ref) : SteelT unit
  (ptr r1 `star` ptr r2)
  (fun _ -> ptr r1 `star` ptr r2)
  = if b then (write r1 0; write r2 0) else (write r2 0);
    write r2 0

let test_if9 (b:bool) (r1 r2: ref) : SteelT unit
  (ptr r1 `star` ptr r2)
  (fun _ -> ptr r1 `star` ptr r2)
  = write r1 0;
    if b then (write r1 0) else (write r2 0);
    write r2 0;
    if b then (write r1 0) else (write r2 0);
    write r1 0

(* Leave out some extra slprop outside of if_then_else *)
let test_if10 (b:bool) (r1 r2 r3: ref) : SteelT unit
  (ptr r1 `star` ptr r2 `star` ptr r3)
  (fun _ -> ptr r1 `star` ptr r2 `star` ptr r3)
  = if b then (write r1 0; write r2 0) else (write r2 0; write r1 0);
    write r2 0

(* Tests if_then_else depending on previously created local var *)
let test_if11 () : SteelT ref emp ptr =
  let r = alloc 0 in
  if true then return r else return r

// Test for refinement types in return values. cf PR 2227
assume
val f_ref (p:prop) :
  SteelT (u:unit{p}) emp (fun _ -> emp)

let g (p:prop)
  : Steel unit emp (fun _ -> emp) (requires fun _ -> True) (ensures fun _ _ _ -> p) =
  let f2 (p:prop)
    : SteelT (u:unit{p}) emp (fun _ -> emp)
    = f_ref p
  in
  let x = f2 p in x


assume
val int_sl ([@@@smt_fallback] n:int) : vprop

assume val int_f (n:int) : SteelT unit (int_sl n) (fun _ -> int_sl n)

let test_subcomp_dep (n:int) : SteelT unit (int_sl n) (fun _ -> int_sl n) =
  int_f (n - 1 + 1);
  int_f n

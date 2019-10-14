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

module RST.Effect.Test

open Steel.Resource
open Steel.RST

open RST.Effect

/// Tests for RST as a layered effect

#set-options "--initial_fuel 2 --max_fuel 2 --initial_ifuel 2 --max_ifuel 2 --using_facts_from '* \
  -FStar.Seq \
  -FStar.ST \
  -FStar.HyperStack \
  -FStar.Monotonic.HyperStack
  -FStar.Heap
  -FStar.Monotonic.Heap \
  -FStar.Tactics \
  -FStar.Reflection \
  -LowStar \
  -FStar.ModifiesGen'"


assume val rst_get (r:resource)
: RST (rmem r)
  r (fun _ -> r)
  (fun _ -> True)
  (fun h0 r h1 -> r == h0 /\ h1 == h0)

let test1 ()
: RST nat emp (fun _ -> emp) (fun _ -> True) (fun _ r _ -> r == 2)
= 2

assume val r1 : r:resource{r.t == nat}
assume val r2 : r:resource{r.t == nat}
assume val r3 : r:resource{r.t == nat}

assume val f1
: x:nat ->
  RST unit r1 (fun _ -> r2)
  (fun (rm:rmem r1) -> rm r1 == 2)
  (fun (rm_in:rmem r1) _ (rm_out:rmem r2) -> rm_out r2 == rm_in r1 + x)

assume val f2
: x:nat ->
  RST unit r2 (fun _ -> r3)
  (fun rm -> rm r2 == 2)
  (fun rm_in _ rm_out -> rm_out r3 == rm_in r2 + x)

assume val f3
: x:nat ->
  RST unit r3 (fun _ -> r3)
  (fun rm -> rm r3 == 2)
  (fun rm_in _ rm_out -> rm_out r3 == rm_in r3 + x)

let test2 ()
: RST unit r1 (fun _ -> r3)
  (fun rm -> rm r1 == 2)
  (fun rm_in x rm_out -> rm_out r3 > 2)
= f1 0; f2 0; f3 3

assume Can_be_split_into_emp:
  forall (r:resource). r `can_be_split_into` (r, emp) /\ r `can_be_split_into` (emp, r)

let test3 ()
: RST nat r1 (fun _ -> r3)
  (fun rm -> rm r1 == 2)
  (fun rm_in x rm_out -> x == 2 /\ rm_out r3 > 2)
= f1 0; f2 0; f3 3;
  let x = rst_frame r3 (fun _ -> r3) r3 test1 in
  let _ = rst_frame r3 (fun _ -> r3) r3 test1 in
  admit ()  //this fails to prove the postcondition because of focus_rmem not working well I think

let test4 ()
: RST unit r1 (fun _ -> r2)
  (fun rm -> rm r1 == 2)
  (fun rm_in x rm_out -> True)
= f1 0; ()  //this works because the lift is parametric in the resource, else () would need to be wrapped in rst_frame

// open FStar.Tactics

// module T = FStar.Tactics

// [@resolve_implicits]
// let resolve_all_implicits () : Tac unit =
//   T.dump "Remaining problems:"

// assume val f_imp
// : unit -> RST unit r1 (fun _ -> r1) (fun _ -> True) (fun _ _ _ -> True)
// assume val g_imp
// : unit -> RST unit r2 (fun _ -> r2) (fun _ -> True) (fun _ _ _ -> True)

// let test_imp ()
// : RST unit (r1 <*> r2) (fun _ -> r1 <*> r2)
//   (fun _ -> True) (fun _ _ _ -> True)
// = rst_frame _ #r1 #(fun _ -> r1) _ _ #(fun _ -> True) #(fun _ _ _ -> True) f_imp;
//   rst_frame _ #r2 #(fun _ -> r2) _ _ #(fun _ -> True) #(fun _ _ _ -> True) g_imp


/// Testing basic pattern matching

assume val test5 (x:int)
: RST unit r1 (fun _ -> r1)
  (fun _ -> x > 0)
  (fun _ _ _ -> True)

let test6 (l:list int)
: RST unit r1 (fun _ -> r1)
  (fun _ -> Cons? l /\ Cons?.hd l > 0)
  (fun _ _ _ -> True)
= match l with
  | hd::_ -> test5 hd

let test7 (l:list (option int))
: RST unit r1 (fun _ -> r1)
  (fun _ -> Cons? l /\ Some? (Cons?.hd l))
  (fun _ _ _ -> True)
= match l with
  | (Some hd)::_ ->
    if hd > 0 then test5 (Some?.v (Cons?.hd l)) else ()


(*** chacha20 ***)

/// The effect definitions and `rst_frame` are as defined in `examples/layered_effect/RST.Effect.fst`

module U32 = FStar.UInt32

assume val array (a:Type0) : Type0
assume val length (#a:Type0) (b:array a) : nat
assume val array_resource (#a:Type0) (b:array a) : resource
assume val as_rseq (#a:Type0) (b:array a) (#r:resource{array_resource b `is_subresource_of` r}) (h:rmem r)
: GTot (s:Seq.seq a{Seq.length s == length b})

assume val index (#a:Type0) (b:array a) (i:U32.t{U32.v i < length b})
: unit ->
  RST a
  (array_resource b)
  (fun _ -> array_resource b)
  (fun _ -> True)
  (fun h0 x h1 ->
    x == Seq.index (as_rseq b h0) (U32.v i) /\
    h0 == h1)

assume val upd (#a:Type0) (b:array a) (i:U32.t{U32.v i < length b}) (v:a)
: unit ->
  RST unit
  (array_resource b)
  (fun _ -> array_resource b)
  (fun _ -> True)
  (fun h0 _ h1 ->
    let s0 = as_rseq b h0 in
    let s1 = as_rseq b h1 in
    Seq.index s1 (U32.v i) == v /\
    (forall (j:nat).{:pattern Seq.index s1 j} (j < Seq.length s1 /\ j =!= (U32.v i)) ==>
              (Seq.index s1 j == Seq.index s0 j)))


type state = b:array U32.t{length b == 16}


/// `focus_rmem` doesn't work well for me, so adding lemmas that I need for chacha20 function below

assume val as_rseq_focus_rmem1 (#a:Type0)
  (b1 b2:array a) (h:rmem (array_resource b1 <*> array_resource b2))
: Lemma (as_rseq b1 h == as_rseq b1 (focus_rmem h (array_resource b1)))
        [SMTPat (as_rseq b1 h)]

assume val as_rseq_focus_rmem2 (#a:Type0)
  (b1 b2:array a) (h:rmem (array_resource b1 <*> array_resource b2))
: Lemma (as_rseq b2 h == as_rseq b2 (focus_rmem h (array_resource b2)))
        [SMTPat (as_rseq b2 h)]

assume val as_rseq_focus_rmem_inv1 (#a:Type0)
  (b1 b2:array a) (h0 h1:rmem (array_resource b1 <*> array_resource b2))
: Lemma
  (requires focus_rmem h0 (array_resource b1) == focus_rmem h1 (array_resource b1))
  (ensures as_rseq b1 h0 == as_rseq b1 h1)
  [SMTPat (focus_rmem h0 (array_resource b1)); SMTPat (focus_rmem h1 (array_resource b1))]

assume val as_rseq_focus_rmem_inv2 (#a:Type0)
  (b1 b2:array a) (h0 h1:rmem (array_resource b1 <*> array_resource b2))
: Lemma
  (requires focus_rmem h0 (array_resource b2) == focus_rmem h1 (array_resource b2))
  (ensures as_rseq b2 h0 == as_rseq b2 h1)
  [SMTPat (focus_rmem h0 (array_resource b2)); SMTPat (focus_rmem h1 (array_resource b2))]


/// `copy_state`

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"
let copy_state
  (st:state)
  (ost:state)
: RST unit
  (array_resource st <*> array_resource ost)
  (fun _ -> array_resource st <*> array_resource ost)
  (fun _ -> True)
  (fun h0 _ h1 ->
    focus_rmem h0 (array_resource ost) == focus_rmem h1 (array_resource ost) /\
    as_rseq st h1 `Seq.equal` as_rseq ost h0)
= let both_st = array_resource st <*> array_resource ost in
  let h0 = rst_get both_st in
  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 0ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 0ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 1ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 1ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 2ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 2ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 3ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 3ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 4ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 4ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 5ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 5ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 6ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 6ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 7ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 7ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 8ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 8ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 9ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 9ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 10ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 10ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 11ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 11ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 12ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 12ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 13ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 13ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 14ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 14ul v);

  let v =
    rst_frame both_st (fun _ -> both_st) (array_resource st)
    (index ost 15ul) in

  rst_frame both_st (fun _ -> both_st) (array_resource ost)
    (upd st 15ul v);

  let h1 = rst_get both_st in

  //assert False;
  Seq.lemma_eq_intro (as_rseq st h1) (as_rseq ost h0)

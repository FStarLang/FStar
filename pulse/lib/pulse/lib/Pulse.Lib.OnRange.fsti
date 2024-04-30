(*
   Copyright 2023 Microsoft Research

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

module Pulse.Lib.OnRange
open Pulse.Lib.Pervasives
open Pulse.Lib.Stick

val on_range (p: (nat -> vprop))
             ([@@@equate_by_smt] i:nat)
             ([@@@equate_by_smt] j:nat)
  : vprop

val on_range_eq_false (p:nat -> vprop) (i j:nat)
: Lemma 
  (requires i > j)
  (ensures on_range p i j == pure False)

val on_range_eq_emp (p:nat -> vprop) (i j:nat)
: Lemma 
  (requires i == j)
  (ensures on_range p i j == emp)

val on_range_eq_cons (p:nat -> vprop) (i j:nat)
: Lemma 
  (requires i < j)
  (ensures on_range p i j == (p i ** on_range p (i + 1) j))

val on_range_is_small (p:nat -> vprop) (i:nat) (j:nat)
  : Lemma (requires forall k. (i <= k /\ k < j) ==> is_small (p k))
          (ensures is_small (on_range p i j))
          [SMTPat (on_range p i j)]

val on_range_is_big (p:nat -> vprop) (i:nat) (j:nat)
  : Lemma (requires forall k. (i <= k /\ k < j) ==> is_big (p k))
          (ensures is_big (on_range p i j))
          [SMTPat (on_range p i j)]

val on_range_le
  (p: (nat -> vprop))
  (#i:nat)
  (#j:nat)
: stt_ghost unit emp_inames
    (requires on_range p i j)
    (ensures fun _ -> on_range p i j ** pure (i <= j))

val on_range_empty
  (p: (nat -> vprop))
  (i: nat)
: stt_ghost unit emp_inames
    (requires emp)
    (ensures fun _ -> on_range p i i)

val on_range_singleton_intro
  (p: (nat -> vprop))
  (i: nat)
: stt_ghost unit emp_inames
    (requires (p i))
    (ensures fun _ -> on_range p i (i + 1))

val on_range_singleton_elim
  ()
  (#p: (nat -> vprop))
  (#i:nat)
  (#j:nat { j == i + 1 })
: stt_ghost unit emp_inames
    (on_range p i j)
    (fun _ -> p i)

val on_range_split
  (j:nat)
  (#p: (nat -> vprop))
  (#i:nat{ i <= j })
  (#k:nat{ j <= k })
: stt_ghost unit emp_inames
    (requires on_range p i k)
    (ensures fun _ -> on_range p i j ** on_range p j k)

val on_range_join
  (i j k: nat)
  (#p: (nat -> vprop))
: stt_ghost unit emp_inames
    (requires on_range p i j ** on_range p j k)
    (ensures fun _ -> on_range p i k)

val on_range_cons
  (i:nat)
  (#p: (nat -> vprop))
  (#j:nat{j == i + 1})
  (#k: nat)
: stt_ghost unit emp_inames
    (p i ** on_range p j k)
    (fun _ -> on_range p i k)

val on_range_uncons
  ()
  (#p: (nat -> vprop))
  (#i:nat)
  (#k:nat { i < k })
: stt_ghost unit emp_inames
    (on_range p i k)
    (fun _ -> p i ** on_range p (i + 1) k)

val on_range_cons_with_implies
  (i:nat)
  (#p: (nat -> vprop))
  (#k: nat)
: stt_ghost unit emp_inames
    (p i ** on_range p (i + 1) k)
    (fun _ ->
      on_range p i k **
      (on_range p i k @==> (p i ** on_range p (i + 1) k))
    )

val on_range_snoc
  ()
  (#p: (nat -> vprop))
  (#i #j:nat)
: stt_ghost unit emp_inames
    (on_range p i j ** p j)
    (fun _ -> on_range p i (j + 1))

val on_range_unsnoc
  ()
  (#p: (nat -> vprop))
  (#i:nat)
  (#k:nat{ i < k })
: stt_ghost unit emp_inames
    (on_range p i k)
    (fun _ -> on_range p i (k - 1) ** p (k - 1))

val on_range_snoc_with_implies
  ()
  (#p: (nat -> vprop))
  (#i:nat)
  (#j:nat)
: stt_ghost unit emp_inames
    (on_range p i j ** p j)
    (fun _ -> on_range p i (j + 1) **  (on_range p i (j + 1) @==> (on_range p i j ** p j)))

val on_range_get
  (j:nat)
  (#p: (nat -> vprop))
  (#i:nat{i <= j})
  (#k:nat{j < k})
: stt_ghost unit emp_inames
    (on_range p i k)
    (fun _ -> on_range p i j ** p j ** on_range p (j + 1) k)

val on_range_put
  (i:nat)
  (j:nat{ i <= j })
  (k:nat{ j < k })
  (#p: (nat -> vprop))
: stt_ghost unit emp_inames
    (on_range p i j ** p j ** on_range p (j + 1) k)
    (fun _ -> on_range p i k)
 
val on_range_focus
  (j:nat)
  (#p: (nat -> vprop))
  (#i:nat{ i <= j })
  (#k:nat{ j < k })
: stt_ghost unit emp_inames
    (on_range p i k)
    (fun _ -> p j ** (p j @==> on_range p i k))

val on_range_weaken_and_shift
  (p p': (nat -> vprop))
  (delta: int)
  (i: nat { i + delta >= 0 })
  (j: nat { j + delta >= 0 })
  (* maybe phi could open some invariants too? *)
  (phi: (k: nat { i <= k /\ k < j }) -> stt_ghost unit emp_inames(p k) (fun _ -> p' (k + delta)))
: stt_ghost unit emp_inames
    (on_range p i j)
    (fun _ -> on_range p' (i + delta) (j + delta))

val on_range_weaken
  (p p': (nat -> vprop))
  (i: nat)
  (j: nat)
  (phi: (k: nat { i <= k /\ k < j }) -> stt_ghost unit emp_inames (p k) (fun _ -> p' k))
: stt_ghost unit emp_inames
    (on_range p i j)
    (fun _ -> on_range p' i j)

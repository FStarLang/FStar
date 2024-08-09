(*
   Copyright 2008-2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Author: Megan Frisella
*)
module FStar.FunctionalQueue

open FStar.Seq

val queue (a:Type u#a) : Type u#a

val empty (#a:Type) : queue a

val queue_to_seq (#a:Type) (q:queue a) : seq a

val queue_of_seq (#a:Type) (s:seq a) : queue a

val equal (#a:Type) (q1 q2:queue a) : prop

let not_empty (#a:Type) (q:queue a) : prop
  = let s = queue_to_seq q in
    ~(Seq.equal s Seq.empty) /\ length s > 0

val lemma_eq_intro: #a:Type -> q1:queue a -> q2:queue a -> Lemma
  (requires Seq.equal (queue_to_seq q1) (queue_to_seq q2))
  (ensures (equal q1 q2))
  [SMTPat (equal q1 q2)]

val lemma_eq_elim: #a:Type -> q1:queue a -> q2:queue a -> Lemma
  (requires (equal q1 q2))
  (ensures queue_to_seq q1 == queue_to_seq q2)
  [SMTPat (equal q1 q2)]

val lemma_seq_queue_bij: #a:Type -> s:seq a -> Lemma
  (queue_to_seq (queue_of_seq s) == s)
  [SMTPat (queue_of_seq s)]

val lemma_queue_seq_bij: #a:Type -> q:queue a -> Lemma
  (equal (queue_of_seq (queue_to_seq q)) q)
  [SMTPat (queue_to_seq q)]

val enqueue (#a:Type) (x:a) (q:queue a) : queue a

val dequeue (#a:Type) (q:queue a{not_empty q}) : a & queue a

val peek (#a:Type) (q:queue a{not_empty q}) : a

val lemma_empty_ok: #a:Type -> Lemma
  (queue_to_seq #a empty == Seq.empty)
  [SMTPat (empty #a)]

val lemma_enqueue_ok: #a:Type -> x:a -> q:queue a -> Lemma
  (queue_to_seq (enqueue x q) == Seq.snoc (queue_to_seq q) x)
  [SMTPat (enqueue x q)]

val lemma_dequeue_ok: #a:Type -> q:queue a{not_empty q} -> Lemma
  (let hd, tl = dequeue q in
   hd == Seq.head (queue_to_seq q) /\
   equal tl (queue_of_seq (Seq.tail (queue_to_seq q))))
  [SMTPat (dequeue q)]

val lemma_peek_ok: #a:Type -> q:queue a{not_empty q} -> Lemma
  (peek q == Seq.head (queue_to_seq q))
  [SMTPat (peek q)]

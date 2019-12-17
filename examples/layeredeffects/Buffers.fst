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

module Buffers


/// Example of a layered effect to work on two buffers
///
/// With layered effects, we can verify code without any Low* in verification scope (see `copy` below)


module Seq = FStar.Seq

open FStar.Integers

open FStar.HyperStack.ST

module HS = FStar.HyperStack

module B = LowStar.Buffer


type u8 = uint_8
type u32 = uint_32


/// The pre- and postconditions only talk about the contents of the buffers
///   (as sequences), and no modifies etc. reasoning

type pre_t (#n1 #n2:nat) = (Seq.lseq u8 n1 & Seq.lseq u8 n2) -> Type0
type post_t (#n1 #n2:nat) (a:Type) = a -> (Seq.lseq u8 n1 & Seq.lseq u8 n2) -> Type0
type wp_t (#n1 #n2:nat) (a:Type) = wp:(post_t #n1 #n2 a -> pre_t #n1 #n2){
  forall p q. (forall x s. p x s ==> q x s) ==> (forall s. wp p s ==> wp q s)
}


let len (b:B.buffer u8) : GTot nat = B.length b


/// The underlying representation
///
/// The effect is indexed by two buffers and a wp
///
/// Encapsulated modifies/equal_stack_domains etc.

type repr (a:Type) (b1 b2:B.buffer u8) (wp:wp_t #(len b1) #(len b2) a) =
  unit -> STATE a (fun p h0 ->
    B.disjoint b1 b2 /\ B.live h0 b1 /\ B.live h0 b2 /\
    wp
      (fun x s1 ->
       forall h1. (s1 == (B.as_seq h1 b1, B.as_seq h1 b2) /\
              B.(modifies (loc_union (loc_buffer b1) (loc_buffer b2)) h0 h1) /\
              equal_domains h0 h1 /\
              B.live h1 b1 /\ B.live h1 b2) ==> p x h1)
      (B.as_seq h0 b1, B.as_seq h0 b2)
  )


/// Combinators

inline_for_extraction
let return (a:Type) (b1 b2:B.buffer u8) (x:a)
: repr a b1 b2 (fun p s -> p x s)
= fun _ -> x

inline_for_extraction
let bind (a:Type) (b:Type)
  (b1 b2:B.buffer u8) (wp_f:wp_t #(len b1) #(len b2) a) (wp_g:a -> wp_t #(len b1) #(len b2) b)
  (f:repr a b1 b2 wp_f) (g:(x:a -> repr b b1 b2 (wp_g x)))
: repr b b1 b2 (fun p -> wp_f (fun x -> (wp_g x) p))
= fun _ ->
  let x = f () in
  (g x) ()

inline_for_extraction
let subcomp (a:Type)
  (b1 b2:B.buffer u8) (wp_f:wp_t #(len b1) #(len b2) a) (wp_g:wp_t #(len b1) #(len b2) a)
  (f:repr a b1 b2 wp_f)
: Pure (repr a b1 b2 wp_g)
  (requires forall p s. wp_g p s ==> wp_f p s)
  (ensures fun _ -> True)
= f

inline_for_extraction
let if_then_else (a:Type)
  (b1 b2:B.buffer u8) (wp_f:wp_t #(len b1) #(len b2) a) (wp_g:wp_t #(len b1) #(len b2) a)
  (f:repr a b1 b2 wp_f) (g:repr a b1 b2 wp_g)
  (p:Type0)
: Type
= repr a b1 b2
  (fun post s ->
    (p ==> wp_f post s) /\
    ((~ p) ==> wp_g post s))


reifiable reflectable
layered_effect {
  CHACHA : a:Type -> b1:B.buffer u8 -> b2:B.buffer u8 -> wp_t #(len b1) #(len b2) a -> Effect
  with
  repr = repr;
  return = return;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}


/// Lift from DIV

let lift_div_chacha (a:Type)
  (b1 b2:B.buffer u8) (wp:pure_wp a{forall p q. (forall x. p x ==> q x) ==> (wp p ==> wp q)})
  (f:unit -> DIV a wp)
: repr a b1 b2 (fun p s -> wp (fun x -> p x s))
= fun _ -> f ()


sub_effect DIV ~> CHACHA = lift_div_chacha

effect Chacha (a:Type)
  (b1 b2:B.buffer u8)
  (pre:(Seq.lseq u8 (len b1) & Seq.lseq u8 (len b2)) -> Type0)
  (post:(Seq.lseq u8 (len b1) & Seq.lseq u8 (len b2)) -> a -> (Seq.lseq u8 (len b1) & Seq.lseq u8 (len b2)) -> Type0)
= CHACHA a b1 b2 (fun p s -> pre s /\ (forall x s1. post s x s1 ==> p x s1))


/// Define actions for the effect that read/write one of the buffers

inline_for_extraction
let read1_ (b1 b2:B.buffer u8) (i:u32)
: repr u8 b1 b2
  (fun p s -> i < B.len b1 /\ (i < B.len b1 ==> p (Seq.index (fst s) (v i)) s))
= fun _ -> B.index b1 i

inline_for_extraction
let read2_ (b1 b2:B.buffer u8) (i:u32)
: repr u8 b1 b2
  (fun p s -> i < B.len b2 /\ (i < B.len b2 ==> p (Seq.index (snd s) (v i)) s))
= fun _ -> B.index b2 i

inline_for_extraction
let write1_ (b1 b2:B.buffer u8) (i:u32) (x:u8)
: repr unit b1 b2
  (fun p s ->
    i < B.len b1 /\ (i < B.len b1 ==> p () (Seq.upd (fst s) (v i) x, snd s)))
= fun _ -> B.upd b1 i x

inline_for_extraction
let write2_ (b1 b2:B.buffer u8) (i:u32) (x:u8)
: repr unit b1 b2
  (fun p s ->
    i < B.len b2 /\ (i < B.len b2 ==> p () (fst s, Seq.upd (snd s) (v i) x)))
= fun _ -> B.upd b2 i x


inline_for_extraction
let read1 (#b1 #b2:B.buffer u8) (i:u32)
: Chacha u8 b1 b2
  (requires fun _ -> i < B.len b1)
  (ensures fun s0 x s1 -> i < B.len b1 /\ x == Seq.index (fst s0) (v i) /\ s1 == s0)
= CHACHA?.reflect (read1_ b1 b2 i)

inline_for_extraction
let read2 (#b1 #b2:B.buffer u8) (i:u32)
: Chacha u8 b1 b2
  (requires fun _ -> i < B.len b2)
  (ensures fun s0 x s1 -> i < B.len b2 /\ x == Seq.index (snd s0) (v i) /\ s1 == s0)
= CHACHA?.reflect (read2_ b1 b2 i)

inline_for_extraction
let write1 (#b1 #b2:B.buffer u8) (i:u32) (x:u8)
: Chacha unit b1 b2
  (requires fun _ -> i < B.len b1)
  (ensures fun s0 _ s1 -> i < B.len b1 /\ s1 == (Seq.upd (fst s0) (v i) x, snd s0))
= CHACHA?.reflect (write1_ b1 b2 i x)

inline_for_extraction
let write2 (#b1 #b2:B.buffer u8) (i:u32) (x:u8)
: Chacha unit b1 b2
  (requires fun _ -> i < B.len b2)
  (ensures fun s0 _ s1 -> i < B.len b2 /\ s1 == (fst s0, Seq.upd (snd s0) (v i) x))
= CHACHA?.reflect (write2_ b1 b2 i x)


/// Finally, we want to copy b1 to b2
///
/// Naive attempt:

[@expect_failure]
noextract
let copy_naive (b1 b2:B.buffer u8)
: ST unit
  (requires fun h -> B.live h b1 /\ B.live h b2 /\ B.disjoint b1 b2 /\ B.length b1 == 16 /\ B.length b2 == 16)
  (ensures fun h0 _ h1 ->
    B.(modifies (loc_buffer b2) h0 h1) /\
    Seq.equal (B.as_seq h1 b2) (B.as_seq h0 b1))
= let x = B.index b1 0ul in B.upd b2 0ul x;
  let x = B.index b1 1ul in B.upd b2 1ul x;
  let x = B.index b1 2ul in B.upd b2 2ul x;
  let x = B.index b1 3ul in B.upd b2 3ul x;
  let x = B.index b1 4ul in B.upd b2 4ul x;
  let x = B.index b1 5ul in B.upd b2 5ul x;
  let x = B.index b1 6ul in B.upd b2 6ul x;
  let x = B.index b1 7ul in B.upd b2 7ul x;
  let x = B.index b1 8ul in B.upd b2 8ul x;
  let x = B.index b1 9ul in B.upd b2 9ul x;
  let x = B.index b1 10ul in B.upd b2 10ul x;
  let x = B.index b1 11ul in B.upd b2 11ul x;
  let x = B.index b1 12ul in B.upd b2 12ul x;
  let x = B.index b1 13ul in B.upd b2 13ul x;
  let x = B.index b1 14ul in B.upd b2 14ul x;
  let x = B.index b1 15ul in B.upd b2 15ul x


#set-options "--using_facts_from '* -LowStar -FStar.HyperStack -FStar.Monotonic -FStar.Heap'"

inline_for_extraction
let copy (b1 b2:B.buffer u8)
: Chacha unit b1 b2
  (requires fun _ -> B.length b1 == 16 /\ B.length b2 == 16)
  (ensures fun s0 _ s1 -> Seq.equal (fst s1) (fst s0) /\ Seq.equal (snd s1) (fst s0))
= let x = read1 0ul in write2 0ul x;
  let x = read1 1ul in write2 1ul x;
  let x = read1 2ul in write2 2ul x;
  let x = read1 3ul in write2 3ul x;
  let x = read1 4ul in write2 4ul x;
  let x = read1 5ul in write2 5ul x;
  let x = read1 6ul in write2 6ul x;
  let x = read1 7ul in write2 7ul x;
  let x = read1 8ul in write2 8ul x;
  let x = read1 9ul in write2 9ul x;
  let x = read1 10ul in write2 10ul x;
  let x = read1 11ul in write2 11ul x;
  let x = read1 12ul in write2 12ul x;
  let x = read1 13ul in write2 13ul x;
  let x = read1 14ul in write2 14ul x;
  let x = read1 15ul in write2 15ul x


let copy_st (b1 b2:B.buffer u8)
: ST unit
  (requires fun h -> B.live h b1 /\ B.live h b2 /\ B.length b1 == 16 /\ B.length b2 == 16 /\ B.disjoint b1 b2)
  (ensures fun h0 _ h1 ->
    Seq.equal (B.as_seq h1 b1) (B.as_seq h0 b1) /\
    Seq.equal (B.as_seq h1 b2) (B.as_seq h0 b1) /\
    B.(modifies (loc_union (loc_buffer b1) (loc_buffer b2)) h0 h1))
= reify (copy b1 b2) ()

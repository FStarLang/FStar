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

module STExn

open FStar.Error

open FStar.Heap
open FStar.ST

type error = string

type result (a:Type) = optResult error (option a)

type pre_t = heap -> Type0
type post_t (a:Type) = result a -> heap -> Type0
type wp_t (a:Type) = post_t a -> pre_t


type repr (a:Type) (wp:wp_t a) =
  unit -> STATE (result a) wp


inline_for_extraction
let return (a:Type) (x:a)
: repr a (fun p h -> p (Correct (Some x)) h)
= fun _ -> Correct (Some x)

assume WP_monotonic_stexn:
  (forall (a:Type) (wp:wp_t a).
     (forall (p q:post_t a).
        (forall (x:result a) (h:heap). p x h ==> q x h) ==>
        (forall (h:heap). wp p h ==> wp q h)))

inline_for_extraction
let bind (a:Type) (b:Type)
  (wp_f:wp_t a) (wp_g:a -> wp_t b)
  (f:repr a wp_f) (g:(x:a -> repr b (wp_g x)))
: repr b
  (fun p h ->
    wp_f (fun r h1 ->
      match r with
      | Error s -> p (Error s) h1
      | Correct None -> p (Correct None) h1
      | Correct (Some x) -> (wp_g x) p h1) h)
= fun _ ->
  let r = f () in
  match r with
  | Error s -> Error s
  | Correct None -> Correct None
  | Correct (Some x) -> (g x) ()

let stronger (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:repr a wp_f)
: Pure (repr a wp_g)
  (requires forall p h. wp_g p h ==> wp_f p h)
  (ensures fun _ -> True)
= f

let conjunction (a:Type)
  (wp_f:wp_t a) (wp_g:wp_t a)
  (f:repr a wp_f) (g:repr a wp_g)
  (p:Type0)
: Type
= repr a
  (fun post h ->
    (p ==> wp_f post h) /\
    ((~ p) ==> wp_g post h))


reifiable reflectable
layered_effect {
  STEXN : a:Type -> wp_t a -> Effect with

  repr = repr;
  return = return;
  bind = bind;
  stronger = stronger;
  conjunction = conjunction
}

assume WP_monotonic_pure:
  (forall (a:Type) (wp:pure_wp a).
     (forall (p q:pure_post a).
        (forall (x:a). p x ==> q x) ==>
        (wp p ==> wp q)))

let lift_div_stexn (a:Type) (wp:pure_wp a) (f:unit -> DIV a wp)
: repr a (fun p h -> wp (fun x -> p (Correct (Some x)) h))
= fun _ -> Correct (Some (f ()))

sub_effect DIV ~> STEXN = lift_div_stexn


let raise0 (#a:Type) (s:string)
: repr a (fun p h -> p (Error s) h)
= fun _ -> Error s


let raise (#a:Type) (s:string)
: STEXN a (fun p h -> p (Error s) h)
= STEXN?.reflect (raise0 #a s)


effect StExn (a:Type) (pre:heap -> Type0) (post:heap -> result a -> heap -> Type0) =
  STEXN a (fun p h -> pre h /\ (forall x h1. post h x h1 ==> p x h1))



module Seq = FStar.Seq

assume val byte : Type0
assume type buffer : Type0

assume val length (h:heap) (b:buffer) : nat
assume val as_seq (h:heap) (b:buffer) : (s:Seq.seq byte{Seq.length s == length h b})

assume val t1 : Type0
assume val t2 (x:t1) : Type0
assume val t3 (x:t1) (y:t2 x) : Type0

assume val size_t1 : nat
assume val size_t2 (x:t1) : nat
assume val size_t3 (x:t1) (y:t2 x) : nat


assume val valid_t1_bytes (x:t1) (s:Seq.seq byte) : Type0
assume val valid_t2_bytes (x:t1) (y:t2 x) (s:Seq.seq byte) : Type0
assume val valid_t3_bytes (x:t1) (y:t2 x) (z:t3 x y) (s:Seq.seq byte) : Type0


assume val parse_t1 (b:buffer) (from:nat)
: StExn t1
  (fun h -> length h b >= from)
  (fun h0 r h1 ->
    match r with
    | Error _ -> True
    | Correct None -> h0 == h1
    | Correct (Some x) ->
      h0 == h1 /\
      length h0 b >= from + size_t1 /\
      valid_t1_bytes x (Seq.slice (as_seq h0 b) from (from + size_t1)))

assume val parse_t2 (b:buffer) (from:nat) (x:t1)
: StExn (t2 x)
  (fun h -> length h b >= from)
  (fun h0 r h1 ->
    match r with
    | Error _ -> True
    | Correct None -> h0 == h1
    | Correct (Some y) ->
      h0 == h1 /\
      length h0 b >= from + size_t2 x /\
      valid_t2_bytes x y (Seq.slice (as_seq h0 b) from (from + size_t2 x)))

assume val parse_t3 (b:buffer) (from:nat) (x:t1) (y:t2 x)
: StExn (t3 x y)
  (fun h -> length h b >= from)
  (fun h0 r h1 ->
    match r with
    | Error _ -> True
    | Correct None -> h0 == h1
    | Correct (Some z) ->
      h0 == h1 /\
      length h0 b >= (from + size_t3 x y) /\
      valid_t3_bytes x y z (Seq.slice (as_seq h0 b) from (from + size_t3 x y)))


let parse_t1_and_t2_and_t3 (b:buffer) (from:nat)
: StExn (x:t1 & y:t2 x & t3 x y)
  (fun h -> length h b >= from)
  (fun h0 r h1 ->
    match r with
    | Error _ -> True
    | Correct None -> h0 == h1
    | Correct (Some (| x, y, z |)) ->
      h0 == h1 /\
      length h0 b >= from + size_t1 + size_t2 x + size_t3 x y /\
      valid_t1_bytes x (Seq.slice (as_seq h0 b) from (from + size_t1)) /\
      valid_t2_bytes x y (Seq.slice (as_seq h0 b) (from + size_t1) (from + size_t1 + size_t2 x)) /\
      valid_t3_bytes x y z (Seq.slice (as_seq h0 b) (from + size_t1 + size_t2 x) (from + size_t1 + size_t2 x + size_t3 x y)))
      
= let x = parse_t1 b from in
  let y = parse_t2 b (from + size_t1) x in
  let z = parse_t3 b (from + size_t1 + size_t2 x) x y in
  (| x, y, z |)


let parse_t1_and_t2_and_t3_st (b:buffer) (from:nat)
: ST (result (x:t1 & y:t2 x & t3 x y))
  (fun h -> length h b >= from)
  (fun h0 r h1 ->
    match r with
    | Error _ -> True
    | Correct None -> h0 == h1
    | Correct (Some (| x, y, z |)) ->
      h0 == h1 /\
      length h0 b >= from + size_t1 + size_t2 x + size_t3 x y /\
      valid_t1_bytes x (Seq.slice (as_seq h0 b) from (from + size_t1)) /\
      valid_t2_bytes x y (Seq.slice (as_seq h0 b) (from + size_t1) (from + size_t1 + size_t2 x)) /\
      valid_t3_bytes x y z (Seq.slice (as_seq h0 b) (from + size_t1 + size_t2 x) (from + size_t1 + size_t2 x + size_t3 x y)))
= reify (parse_t1_and_t2_and_t3 b from) ()


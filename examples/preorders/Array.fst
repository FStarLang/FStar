module POPL18.Array

open FStar.ST
open FStar.Heap
open FStar.Seq
module Set = FStar.Set
module Seq = FStar.Seq
module P = FStar.Preorder

type t (a:Type) (n:nat) = s:seq (option a){Seq.length s = n}
let rel0 (#a:Type) (#n:nat) : P.relation (t a n) = fun (s1 s2 : t a n) ->
    forall (i:nat{i < n}). Some? (Seq.index s1 i) ==> Some? (Seq.index s2 i)

let rel_preorder (#a:Type) (#n:nat) : Lemma (P.preorder_rel (rel0 #a #n)) = ()
let rel (#a:Type) (#n:nat) : P.preorder (t a n) = rel_preorder #a #n ; rel0

noeq
type array_ (n:nat) (a:Type) : Type =
  | Array: r:mref (t a n) rel -> offset:nat{offset <= n} -> array_ n a

let array = array_

let fresh (#a:Type) (#n:nat) (x:array n a) (h0 h1:heap) = fresh (Array?.r x) h0 h1

let create a n =
  let h0 = get () in
  let x : t a n = Seq.create n None in
  lemma_alloc rel h0 x true ;
  Array (alloc rel h0 x true) 0
(* let suffix #a #n (Array r o) o' = Array r (o + o') *)
(* let initialized #a #n (Array r o) i h = Some? (Seq.index h.[r] (o + i)) *)
(* let init_at #a #n x i = witnessed (initialized x i) *)
(* let all_init (#n:nat) (#a:Type) (x:array n a) = forall (i:index x). x `init_at` i *)
(* let iarray n a = x:array n a {all_init x} *)
(* let write #a #n (Array r o) i v = r := (Seq.upd !r (o + i) (Some v)); witness (initialized (Array r o) i) *)
(* let read #a #n (Array r o) i = recall (initialized (Array r o) i); Some?.v (!r.[o + i]) *)

module Array

open FStar.ST
open FStar.Heap
open FStar.Preorder
module Seq = FStar.Seq
module Set = FStar.Set

val array: nat -> Type0 -> Type0

val fresh (#a:Type) (#n:nat) (x:array n a) (h0 h1:heap) : Type0

(* [create a n]: allocate a new uninitialized `array a` of size `n` *)
val create: a:Type -> n:nat -> ST (array n a)
    (requires (fun _ -> True))
    (ensures (fun h0 x h1 -> fresh x h0 h1 /\ modifies Set.empty h0 h1))
(* (\* [index x]: the type of a within--bounds index of x *\) *)
(* let index (#a:Type) (#n:nat) (x:array n a) = i:nat{i < n} *)
(* (\* [suffix x i]: obtain a reference to the array starting from offset `i` *\) *)
(* val suffix: #a:Type -> #n:nat -> x:array n a -> i:index x -> array (n - i) a *)
(* (\*  [h.[x]] : View a possibly uninitialized array `x` in state `h` as a sequence *\) *)
(* val op_String_Access : #a:Type -> #n:nat -> heap -> array n a -> Ghost (s:Seq.seq (option a){Seq.length s = n}) *)

(* (\* [x `init_at` i]: a predicate claiming that `x` is initialized at `i` *\) *)
(* val init_at: #a:Type -> #n:nat -> x:array n a -> i:index x -> Type *)
(* (\* [write x i v]: write to `x.(i)`;` `x` is now initialized at `i` *\) *)
(* val write: #a:Type -> #n:nat -> x:array n a -> i:index x -> v:a -> ST unit *)
(*     (ensures  (fun h0 _ h1 -> modifies (Set.singleton x) h0 h1 /\ h1.[x] == Seq.upd h0.[x] i (Some v) /\ x `init_at` i)) *)
(* (\* [read x i]: can only read from index `i` of `x` if it is initialized *\) *)
(* val read: #a:Type -> #n:nat -> x:array n a -> i:index x{x `init_at` i} -> ST a *)
(*     (ensures (fun h0 r h1 -> modifies Set.empty h0 h1 /\ Some r = Seq.index h0.[x] i)) *)

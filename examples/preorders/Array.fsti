module Array

open FStar.Heap
open FStar.ST
open FStar.Preorder
module Seq = FStar.Seq
module Set = FStar.Set

val array: nat -> Type0 -> Type0

val fresh (#a:Type) (#n:nat) (x:array n a) (h0 h1:heap) : Type0
val addr_of: #a:Type0 -> #n:nat -> array n a -> GTot nat

(* [create a n]: allocate a new uninitialized `array a` of size `n` *)
val create: a:Type -> n:nat -> ST (array n a)
    (requires (fun _ -> True))
    (ensures (fun h0 x h1 -> fresh x h0 h1 /\ modifies Set.empty h0 h1))

(* [index x]: the type of a within--bounds index of x *)
let index (#a:Type) (#n:nat) (x:array n a) = i:nat{i < n}

val sub: #a:Type -> #n:nat -> x:array n a -> i:index x -> len:nat{i + len <= n} -> array len a

let suffix (#a:Type) (#n:nat) (x:array n a) (i:index x) :array (n - i) a = sub x i (n - i)

let prefix (#a:Type) (#n:nat) (x:array n a) (i:index x) :array i a = sub x 0 i

(*  [h.[x]] : View a possibly uninitialized array `x` in state `h` as a sequence *)
val op_String_Access : #a:Type -> #n:nat -> heap -> array n a -> GTot (s:Seq.seq (option a){Seq.length s == n})
val as_seq : #a:Type -> #n:nat -> heap -> array n a -> GTot (s:Seq.seq (option a){Seq.length s == n})

(* [x `init_at` i]: a predicate claiming that `x` is initialized at `i` *)
val init_at: #a:Type -> #n:nat -> x:array n a -> i:index x -> Type0
(* [write x i v]: write to `x.(i)`;` `x` is now initialized at `i` *)
val write: #a:Type -> #n:nat -> x:array n a -> i:index x -> v:a -> ST unit
    (requires (fun _ -> True))
    (ensures  (fun h0 _ h1 -> modifies (Set.singleton (addr_of x)) h0 h1 /\ h1.[x] == Seq.upd h0.[x] i (Some v) /\ x `init_at` i))
(* [read x i]: can only read from index `i` of `x` if it is initialized *)
val read: #a:Type -> #n:nat -> x:array n a -> i:index x{x `init_at` i} -> ST a
    (requires (fun _ -> True))
    (ensures (fun h0 r h1 -> modifies Set.empty h0 h1 /\ Some r == Seq.index h0.[x] i))

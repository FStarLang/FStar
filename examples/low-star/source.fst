(*--build-config
    options:--admit_fsi Set --admit_fsi Seq --verify_module Source;
    other-files:FStar.Classical.fst FStar.FunctionalExtensionality.fst FStar.Set.fsi seq.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst FStar.SeqProperties.fst
  --*)


module Source

open Seq

type list (a:Type) = 
  | Nil
  | Cons: hd:a -> tl:list a -> list a

type pair (a:Type) (b:Type) = | Pair: fst:a -> snd:b -> pair a b

type option (a:Type) =
  | None
  | Some : v:a -> option a

(* Array with immutable length (check how to works out) *)
type array (a:Type) = | Array : l:nat -> c:ref (s:seq a{Seq.length s = l})  -> array a

(* Test type, not polymorphic *)
type t = 
  | A
  | B
  | C: x:int -> t
  | D: x:int -> y:char -> t



(*** Function experiements ***)
let fst (Pair x y) = x

val proj: #a:Type -> o:option a{ is_Some o} -> Tot a
let proj o =
  Some.v o

val proj_int: o:option int{ is_Some o } -> Tot int
let proj_int o = 
  Some.v o

let head l =
  match l with
  | Nil -> None
  | Cons hd tl -> Some hd

let tail l =
  match l with
  | Nil -> None
  | Cons hd tl -> Some tl

let pattern_match t =
  match t with
  | A -> "A"
  | B -> "B"
  | C _ -> "C"
  | D _ _ -> "D"



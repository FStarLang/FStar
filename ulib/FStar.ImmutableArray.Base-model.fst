(* Model implementation of FStar.ImmutableArray.Base: verified, but never extracted (the real implementation is native).
   An array is modeled as a list. *)
module FStar.ImmutableArray.Base

type t ([@@@strictly_positive] a:Type u#a) : Type u#a = | A : l:list a -> t a

let array_has_eq _ = ()
let of_list l = A l
let length s = FStar.List.Tot.length (A?.l s)
let index s i = FStar.List.Tot.index (A?.l s) i

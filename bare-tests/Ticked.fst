module Ticked

open Prims
open FStar.Attributes

let f (x : 'a) : 'a = x

let g (x : 'a) : 'a = f x

let h : _:'a -> 'a = fun x -> x

(* Should probably forbid this *)
type endo 'a = 'a -> 'a
let endo2 = fun x -> x -> x

[@@expect_failure] // should fail DIFFERENTLY
let endo3 = fun 'a -> 'a -> 'a 

let test : endo int = fun x -> x + 1

type gox a = | Mkgox : a -> gox a

type box 'a = | Mkbox : 'a -> box 'a

type box2 'a = | Mkbox2 of 'a

type tuple2 'a 'b = | Mktuple2 : _1: 'a -> _2: 'b -> tuple2 'a 'b

let box_map f (x : box 'a) = let Mkbox v = x in Mkbox (f v)

(* We should not quantify 'a for f, only for g. *)
let ff0 (x : int) : int =
  let g : 'a -> 'a = fun y -> y in
  g x

let ff1 (x : int) : int =
  let g (x : 'a) : 'a = x in
  g x

let noconfuse (f : 'a -> 'a) (x : 'a) : 'a =
  (* g is NOT polymorphic. *)
  let g : 'a -> 'a = fun _ -> x in
  g x

let noconfuse2 (f : 'a -> 'a) (x : 'a) : 'a =
  (* g is NOT polymorphic. *)
  let g : 'a -> 'a =
    let h : 'a -> 'a =
      fun _ -> x
    in
    h
  in
  g x

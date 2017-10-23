module Test

open Squash

(* Testing that our standard library doesn't shadow local modules *)

let z : int = x

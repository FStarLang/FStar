module Deref2

open Steel.Effect
open Steel.Reference

let test1 () : SteelT UInt32.t emp (fun _ -> emp)
= let r = malloc 0ul in
  let x = read r in
  free r;
  x

let main : Int32.t = 0l

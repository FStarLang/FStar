module FsSplitLo

/// Section 122.18.  The upstream half of the F# split test.  It holds one of
/// each thing whose spelling changes when the output is split: a variant, a
/// record, an exception and a polymorphic function, which monomorphization
/// specializes twice so that the two clones cannot both be at home.

type color = | Red | Green

exception Bad of string

type pt = { px : int; py : int }

let flip (c : color) : color =
  match c with
  | Red -> Green
  | Green -> Red

let origin : pt = { px = 0; py = 1 }

let twice (#a : Type) (f : a -> a) (x : a) : a = f (f x)

let add_one (n : int) : int = n + 1

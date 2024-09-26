module Bug172

#lang-pulse

let test (f : int -> int) (x : int) =
  f <| x

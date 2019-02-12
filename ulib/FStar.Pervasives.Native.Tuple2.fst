module FStar.Pervasives.Native.Tuple2
open Prims
(* 'a * 'b *)
type tuple2 'a 'b =
  | Mktuple2: _1:'a -> _2:'b -> tuple2 'a 'b

module CherryEtaValue
open FStar.All
module U32 = FStar.UInt32

(* Eta-reduced to [fun s1 -> FStar.String.compare s1], and also used as a
   value below: the direct call must still be given both arguments rather
   than building a partial application. *)
let cmp (s1 s2: string) : int = FStar.String.compare s1 s2

let sorted : list string = List.Tot.sortWith cmp ["b"; "a"; "c"]

let main () : ML U32.t =
  if cmp "a" "b" < 0 && sorted = ["a"; "b"; "c"] then 0ul else 1ul

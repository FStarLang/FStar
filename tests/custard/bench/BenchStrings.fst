module BenchStrings
(* Building strings: formatting numbers, and concatenation onto an
   accumulator.  (No substrings or indexing: the OCaml library's strings are
   UTF-8, so those are linear there.) *)
module U32 = FStar.UInt32

let rec fmt (i: int) (acc: int) : Tot int (decreases (if i <= 0 then 0 else i)) =
  if i <= 0 then acc else
  let s = string_of_int i ^ ":" ^ string_of_int (i * i) ^ ";" in
  fmt (i - 1) (acc + String.strlen s)

let rec join (l: list string) (acc: string) : string =
  match l with [] -> acc | x :: t -> join t (acc ^ x ^ ",")

let rec words (i: int) (acc: list string) : Tot (list string) (decreases (if i <= 0 then 0 else i)) =
  if i <= 0 then acc else words (i - 1) (string_of_int i :: acc)

let rec repeat (k: int) (ws: list string) (acc: int) : Tot int (decreases (if k <= 0 then 0 else k)) =
  if k <= 0 then acc else repeat (k - 1) ws (acc + String.strlen (join ws ""))

let main () : U32.t =
  let a = fmt 300000 0 in
  let b = repeat 50 (words 5000 []) 0 in
  if a = 5442656 && b = 1194650 then 0ul else 1ul

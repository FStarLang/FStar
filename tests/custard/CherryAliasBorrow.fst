module CherryAliasBorrow
module U32 = FStar.UInt32
open FStar.All

[@@FStar.Attributes.cherry_boxed]
noeq type node = { name: string; kids: list string }

(* A field of an owned boxed value is borrowed from it (cherry.md,
   "Borrowing from an owned value"), and so are the fields of that field:
   none of them is counted, and the node is released after their last use. *)
let first_len ([@@@cherry_owned] n: node) : int =
  let ks = n.kids in
  match ks with
  | k :: _ -> FStar.String.length k + FStar.String.length n.name
  | [] -> 0

(* A field passed on owned is counted, and the node is released before the
   call, which stays a tail call. *)
let rec count (l: list string) (acc: int) : int =
  match l with
  | [] -> acc
  | _ :: tl -> count tl (acc + 1)

let kids_count ([@@@cherry_owned] n: node) : int =
  count n.kids 0

let mk (s: string) : node =
  { name = s; kids = [FStar.String.concat "" ["a"; "b"]; "cde"] }

let main () : ML U32.t =
  let a = first_len (mk "xyz") in
  let b = kids_count (mk "w") in
  if a = 5 && b = 2 then 0ul else 1ul

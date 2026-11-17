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

(* A leaf that no chain of tail calls leads back from borrows its argument
   (cherry.md, "Borrow inference"): the field is passed uncounted, and the
   node is released after the call. *)
let rec count (l: list string) (acc: int) : int =
  match l with
  | [] -> acc
  | _ :: tl -> count tl (acc + 1)

let kids_count ([@@@cherry_owned] n: node) : int =
  count n.kids 0

(* In a loop of tail calls the field is passed on owned, and the node is
   released before the call, which stays a tail call. *)
let rec walk ([@@@cherry_owned] n: node) (acc: int) : Dv int =
  walk_kids n.kids acc
and walk_kids (l: list string) (acc: int) : Dv int =
  match l with
  | [] -> acc
  | k :: tl -> walk ({ name = k; kids = tl }) (acc + 1)

let mk (s: string) : node =
  { name = s; kids = [FStar.String.concat "" ["a"; "b"]; "cde"] }

let main () : ML U32.t =
  let a = first_len (mk "xyz") in
  let b = kids_count (mk "w") in
  let c = walk (mk "v") 0 in
  if a = 5 && b = 2 && c = 2 then 0ul else 1ul

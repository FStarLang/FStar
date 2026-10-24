module CherryList
module U32 = FStar.UInt32

let rec length (l: list U32.t) : U32.t =
  match l with
  | [] -> 0ul
  | _ :: tl -> U32.add_mod 1ul (length tl)

let rec sum (l: list U32.t) : U32.t =
  match l with
  | [] -> 0ul
  | x :: tl -> U32.add_mod x (sum tl)

let rec map_inc (l: list U32.t) : list U32.t =
  match l with
  | [] -> []
  | x :: tl -> U32.add_mod x 1ul :: map_inc tl

let rec append (a b: list U32.t) : list U32.t =
  match a with
  | [] -> b
  | x :: tl -> x :: append tl b

let rec rev_onto (a acc: list U32.t) : list U32.t =
  match a with
  | [] -> acc
  | x :: tl -> rev_onto tl (x :: acc)

let rec range (n: U32.t) : Tot (list U32.t) (decreases U32.v n) =
  if n = 0ul then [] else n :: range (U32.sub n 1ul)

let main () : U32.t =
  let l = range 10ul in
  let m = map_inc l in
  let a = append l m in
  let r = rev_onto a [] in
  if sum r = 120ul && length a = 20ul && sum l = 55ul then 0ul else 1ul

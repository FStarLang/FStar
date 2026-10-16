module CherryIArray
module U32 = FStar.UInt32
module A = FStar.ImmutableArray
open FStar.All

(* Immutable arrays (cherry.md, "Arrays"): [upd] and [push] change an array
   in place when nothing else refers to it, and copy it otherwise, so the old
   value of a shared or global array is still there afterwards.  A million
   pushes in place take linear time; copying each time would not finish.
   The inputs come through [hide] so that extraction cannot fold them. *)
let hide (#a: Type) (x: a) : ML a = x

let rec fill (a: A.t int) (n: nat) : Tot (A.t int) (decreases n) =
  if n = 0 then a else fill (A.push a n) (n - 1)

let rec sum (a: A.t int) (i: nat) (acc: int)
  : Tot int (decreases (if i < A.length a then A.length a - i else 0)) =
  if i < A.length a then sum a (i + 1) (acc + A.index a i) else acc

let rec bump (a: A.t int) (i: nat)
  : Tot (A.t int) (decreases (if i < A.length a then A.length a - i else 0)) =
  if i < A.length a then begin
    A.length_upd a i (A.index a i + 1);
    bump (A.upd a i (A.index a i + 1)) (i + 1)
  end else a

let rec cat (l: list string) : string =
  match l with [] -> "" | x :: r -> x ^ cat r

let rec cats (l: list (list string)) : string =
  match l with [] -> "" | x :: r -> cat x ^ ";" ^ cats r

let rec lists (l: list (A.t string)) : list (list string) =
  match l with [] -> [] | x :: r -> A.to_list x :: lists r

(* A global, which is persistent once computed: updating it copies. *)
let g : A.t string = A.of_list ["x"; "y"; "z"]

let set (#a: Type) (s: A.t a) (i: nat) (v: a) : A.t a =
  if i < A.length s then A.upd s i v else s

let main () : ML U32.t =
  let n = 1000000 in
  let a = fill (hide (A.of_list [])) n in
  let s = sum a 0 0 in
  (* [a] is still used below, so the first pass copies it once. *)
  let b = bump a 0 in
  let c = bump b 0 in
  let ok1 = s = 500000500000 && sum a 0 0 = s && sum c 0 0 = s + 2 * n &&
            A.length c = n in
  (* Counted elements: the replaced one is released, the others shared. *)
  let l : A.t (list string) = hide (A.of_list [["a"; "b"]; ["c"]]) in
  let l2 = set l 1 ["d"; "e"] in
  let l3 = A.push l2 ["f"] in
  let ok2 = cats (A.to_list l) = "ab;c;" && cats (A.to_list l3) = "ab;de;f;" in
  (* Arrays of arrays. *)
  let m : A.t (A.t string) = A.push (A.push (hide (A.of_list [])) g) (set g 0 "w") in
  let m2 = set m 0 (A.push g "q") in
  let ok3 = cats (lists (A.to_list m2)) = "xyzq;wyz;" &&
            cats (lists (A.to_list m)) = "xyz;wyz;" &&
            cat (A.to_list g) = "xyz" in
  if ok1 && ok2 && ok3 then 0ul else 1ul

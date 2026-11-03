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

(* An array in a global reference is shared.  Taken out of the reference
   (FStarC.Array's [set]), so that this is its only reference, it is updated
   in place all the same, and what is stored into it is made shared:
   copying it at each of the 200000 updates below would take minutes.  One still referred to elsewhere is copied.  (It starts as
   [None]: a global's initial value is persistent, and never freed.) *)
let tbl : ref (option (A.t (list string))) = alloc None

let tbl_get () : ML (A.t (list string)) =
  match !tbl with Some a -> a | None -> A.of_list []

let tbl_set (i: nat) (v: string) : ML unit =
  let cur = tbl_get () in
  tbl := None;
  tbl := Some (set cur i (if i < A.length cur then v :: A.index cur i else [v]))

let rec tbl_fill (a: A.t (list string)) (n: nat) : Tot (A.t (list string)) (decreases n) =
  if n = 0 then a else tbl_fill (A.push a []) (n - 1)

let at (a: A.t (list string)) (i: nat) : list string =
  if i < A.length a then A.index a i else []

let rec tbl_loop (i n: nat) : ML unit =
  if i < n then (tbl_set i (hide "v"); tbl_loop (i + 1) n)

let rec tbl_count (a: A.t (list string)) (i: nat) (acc: nat)
  : Tot nat (decreases (if i < A.length a then A.length a - i else 0)) =
  if i < A.length a then tbl_count a (i + 1) (acc + List.Tot.length (A.index a i)) else acc

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
  let k = 200000 in
  tbl := Some (tbl_fill (hide (A.of_list [])) k);
  tbl_loop 0 k;
  let snap = tbl_get () in
  tbl_set 0 (hide "w");
  let cur = tbl_get () in
  let ok4 = tbl_count snap 0 0 = k && tbl_count cur 0 0 = k + 1 &&
            cat (at cur 0) = "wv" && cat (at snap 0) = "v" in
  if ok1 && ok2 && ok3 && ok4 then 0ul else 1ul

module CherryMoveFields
module U32 = FStar.UInt32
open FStar.All

(* A match that owns an unboxed value which dies takes its fields
   (cherry.md, "Calling convention"); the ones it does not use are released. *)
noeq type r = { a: string; b: list int; c: int; d: list string }

let swap (p: list int & string) : string & list int =
  let (x, y) = p in (y, x)

let first (p: list int & string & list int) : list int =
  match p with (x, _, _) -> x

let take_b (v: r) : list int =
  match v with { b = b } -> b

let opt (o: option (list int)) : list int =
  match o with Some l -> l | None -> []

let mk (n: int) : list int = [n; n + 1]

let main () : ML U32.t =
  let s, l = swap (mk 1, FStar.String.concat "" ["a"; "b"]) in
  let f = first (mk 2, "x", mk 3) in
  let b = take_b { a = FStar.String.concat "" ["c"; "d"]; b = mk 4; c = 5; d = ["e"] } in
  let o = opt (Some (mk 6)) in
  let n = opt None in
  if s = "ab" && l = [1; 2] && f = [2; 3] && b = [4; 5] && o = [6; 7] && n = [] then 0ul else 1ul

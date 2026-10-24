module CherryOpt
module U32 = FStar.UInt32

type pair = { name: U32.t; items: list U32.t }

let rec find (x: U32.t) (l: list U32.t) : option (list U32.t) =
  match l with
  | [] -> None
  | y :: tl -> if x = y then Some tl else find x tl

let rec len (l: list U32.t) : U32.t =
  match l with
  | [] -> 0ul
  | _ :: tl -> U32.add_mod 1ul (len tl)

let mk (n: U32.t) (l: list U32.t) : pair = { name = n; items = l }

let push (p: pair) (x: U32.t) : pair = { p with items = x :: p.items }

let main () : U32.t =
  let l = [1ul; 2ul; 3ul; 4ul] in
  let p = mk 7ul l in
  let q = push p 0ul in
  let r = match find 2ul q.items with
    | Some rest -> len rest
    | None -> 99ul in
  let s = match find 9ul l with
    | Some _ -> 1ul
    | None -> 0ul in
  if r = 2ul && s = 0ul && len p.items = 4ul && len q.items = 5ul && q.name = 7ul
  then 0ul else 1ul

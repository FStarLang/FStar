module CherryDeep
module U32 = FStar.UInt32
open FStar.All

(* Values far deeper than the C stack: freeing and marking them must not
   recurse.  The test runs with a small stack, compiled with -O2 so that the
   tail calls building them are loops. *)
let rec build (n: nat) (acc: list int) : list int =
  if n = 0 then acc else build (n - 1) (n :: acc)

(* Left-deep: the loop in the free function follows the right field, so the
   left ones go through the work list. *)
type tree = | Leaf | Node : tree -> int -> tree -> tree
let rec lefty (n: nat) (t: tree) : tree =
  if n = 0 then t else lefty (n - 1) (Node t n Leaf)

(* A chain of closures, each capturing the previous one. *)
let rec chain (n: nat) (f: unit -> int) : (unit -> int) =
  if n = 0 then f else chain (n - 1) (fun () -> f () + 0)

(* A chain through references. *)
noeq type rnode = | REnd : int -> rnode | RCons : ref rnode -> rnode
let rec rchain (n: nat) (r: rnode) : ML rnode =
  if n = 0 then r else rchain (n - 1) (RCons (alloc r))

(* Writing a value into a global reference marks it shared. *)
let keep : ref (list int) = alloc []

let main () : ML U32.t =
  let l = build 1000000 [] in
  let t = lefty 1000000 Leaf in
  let f = chain 300000 (fun () -> 7) in
  let r = rchain 300000 (REnd 0) in
  keep := build 1000000 [];
  let ok = (match l with x :: _ -> x = 1 | [] -> false) &&
           (match t with Node _ k _ -> k = 1 | Leaf -> false) &&
           RCons? r &&
           (* FStar.List.Tot.length must not recurse either (issue #4789). *)
           FStar.List.Tot.length l = 1000000 in
  let _ = f in
  keep := [];
  if ok then 0ul else 1ul

module CherryRef
module U32 = FStar.UInt32
open FStar.All
module IA = FStar.ImmutableArray

let rec len (#a: Type) (l: list a) : nat = match l with [] -> 0 | _ :: t -> 1 + len t

(* A global reference: persistent, so it goes through the lock. *)
let log : ref (list string) = alloc []
let say (s: string) : ML unit = log := s :: !log

(* References inside data, and data inside references. *)
noeq type node = { name: string; next: ref (option node) }

let rec chain_len (n: node) : ML nat =
  match !(n.next) with None -> 1 | Some m -> 1 + chain_len m

(* A closure capturing a reference: a counter. *)
let counter () : ML (unit -> ML int) =
  let c = alloc 0 in
  fun () -> c := !c + 1; !c

(* A reference to a reference, and one holding a closure. *)
let twice (r: ref (ref string)) : ML unit =
  let inner = !r in
  inner := !inner ^ !inner;
  r := alloc (!inner ^ "!")

(* Reads that only index the array peek at the reference (no count): a
   local cell directly, the persistent [tbl] under its lock. *)
let at ([@@@FStar.Attributes.cherry_borrowed] r: ref (IA.t string)) (i: nat) : ML string =
  let a = !r in
  if i < IA.length a then IA.index a i else "?"

let tbl : ref (IA.t string) = alloc (IA.of_list ["p"; "q"])

let main () : ML U32.t =
  say "a"; say ("b" ^ "c");
  let n3 = { name = "c"; next = alloc None } in
  let n2 = { name = "b"; next = alloc (Some n3) } in
  let n1 = { name = "a"; next = alloc (Some n2) } in
  let l1 = chain_len n1 in
  n2.next := None;
  let l2 = chain_len n1 in
  let next = counter () in
  let _ = next () in
  let _ = next () in
  let k = next () in
  let rr = alloc (alloc "x") in
  twice rr;
  let s = !(!rr) in
  let f = alloc (fun (x: int) -> x + 1) in
  f := (let g = !f in fun x -> g (g x));
  let v = !f 10 in
  let big = alloc 100000000000 in
  big := !big * !big;
  let la = alloc (IA.of_list ["u" ^ "v"; "w"]) in
  let p = at la 0 ^ at la 1 ^ at la 2 ^ at tbl 1 in
  la := IA.of_list [];
  let p = p ^ at la 0 ^ at tbl 0 in
  if len !log = 2 && l1 = 3 && l2 = 2 && k = 3 && s = "xx!" && v = 12 &&
     !big = 10000000000000000000000 && n1.name = "a" &&
     p = "uvw?q?p"
  then 0ul else 1ul

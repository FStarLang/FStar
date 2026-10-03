module RecDisp

(* Section 105.  The dispatcher over §104's five identity functions.

   Two things stood between it and collapsing, and only the second was about
   the law: each branch rebuilds from a *call* rather than from its pattern
   variable, and a variant's match has one branch per constructor. *)

module U32 = FStar.UInt32
module G = FStar.Ghost

noeq type str = { s_sz : U32.t; s_perm : G.erased nat }
noeq type arr = { a_n : U32.t; a_perm : G.erased nat }

noeq type raw =
  | Str of str
  | Arr of arr
  | Int of U32.t

(* Section 104 makes each of these [return c;].  They are plain [let]s, so
   without section 105.1 they stay functions and the dispatcher's branches
   rebuild from a call. *)
let str_reset (p: G.erased nat) (c: str) : str = { c with s_perm = p }
let arr_reset (p: G.erased nat) (c: arr) : arr = { c with a_perm = p }

(* The dispatcher.  [cbor_raw_reset_perm_tot], to the shape. *)
let reset (p: G.erased nat) (c: raw) : raw =
  match c with
  | Str v -> Str (str_reset p v)
  | Arr v -> Arr (arr_reset p v)
  | _ -> c

(* Exhaustive without a catch-all: the other way a match covers its type. *)
let reset_all (p: G.erased nat) (c: raw) : raw =
  match c with
  | Str v -> Str (str_reset p v)
  | Arr v -> Arr (arr_reset p v)
  | Int n -> Int n

(* The permutation one level up, and the reason the law reads constructor
   names rather than counting branches: this has exactly the shape above and
   is not the identity. *)
type two = | L of U32.t | R of U32.t

let swap2 (c: two) : two =
  match c with
  | L x -> R x
  | R x -> L x

(* One branch that is not a rebuild is enough to stop it. *)
let bump_int (c: raw) : raw =
  match c with
  | Int n -> Int (U32.add_mod n 1ul)
  | _ -> c

let tag (c: raw) : U32.t = match c with Str _ -> 0ul | Arr _ -> 1ul | Int _ -> 2ul
let tag2 (c: two) : U32.t = match c with L _ -> 0ul | R _ -> 1ul

let main () : FStar.Int32.t =
  let a = reset (G.hide 1) (Str { s_sz = 4ul; s_perm = G.hide 0 }) in
  let b = reset_all (G.hide 1) (Int 9ul) in
  let c = swap2 (L 3ul) in
  let d = bump_int (Int 7ul) in
  if tag a = 0ul && tag b = 2ul && tag2 c = 1ul && tag d = 2ul
  then 0l else 1l

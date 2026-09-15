module CDeadLet
module U32 = FStar.UInt32
module I32 = FStar.Int32
open FStar.All

(* Section 19.5: a binding nothing reads.  A pattern match names the fields of
   the constructor it matched, and a body is under no obligation to use any of
   them -- [| Pair _ _ -> 0ul] is the extreme case, and F* code writes it all
   the time.  The match compiler still emits the binding, so the C came out
   with a declaration and an initializer and no use, which a build with
   [-Werror=unused-variable] refuses to compile.  These tests already compile
   with [-Wall -Wextra -Werror], so this file failing to build *is* the
   assertion.

   The elimination is a fact about C rather than about the IR, so it lives in
   the printer: an unread binding whose initializer is pure simply does not
   get emitted.  Purity is the side condition that matters -- an initializer
   that does something still has to run, and one that does not can go with
   the name. *)

noeq type point = { px : U32.t; py : U32.t }

noeq type shape =
  | Circle : U32.t -> shape
  | Rect   : point -> U32.t -> shape

(* Every field of the matched constructor goes unused. *)
let tag_of (s : shape) : ML U32.t =
  match s with
  | Circle _ -> 1ul
  | Rect _ _ -> 2ul

(* A record pattern, likewise: the binding is an alias of the scrutinee and
   nothing reads it. *)
let width_or (p : point) (dflt : U32.t) : ML U32.t =
  let { px = _ ; py = _ } = p in dflt

(* One field used and one not, so the surviving binding is genuinely needed
   and only the dead one may be dropped. *)
let area_ish (s : shape) : ML U32.t =
  match s with
  | Circle r -> U32.mul_mod r r
  | Rect _ h -> h

let main () : ML I32.t =
  let p = { px = 3ul; py = 4ul } in
  let a = tag_of (Circle 1ul) in
  let b = tag_of (Rect p 5ul) in
  let c = width_or p 7ul in
  let d = area_ish (Rect p 9ul) in
  if U32.eq a 1ul && U32.eq b 2ul && U32.eq c 7ul && U32.eq d 9ul
  then 0l else 1l

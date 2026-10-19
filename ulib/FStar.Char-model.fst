(* Model implementation of FStar.Char: verified, but never extracted (the real implementation is native).
   A char is modeled as its code point. Case conversion only handles ASCII letters. *)
module FStar.Char

module U32 = FStar.UInt32

type char : eqtype =
  | Char : code:U32.t{U32.v code < 0xd7ff \/ (U32.v code >= 0xe000 /\ U32.v code <= 0x10ffff)} -> char

let u32_of_char c = Char?.code c
let char_of_u32 c = Char c
let char_of_u32_of_char _ = ()
let u32_of_char_of_u32 _ = ()

let lowercase c =
  let n = U32.v (Char?.code c) in
  if 65 <= n && n <= 90 then Char (U32.uint_to_t (n + 32)) else c

let uppercase c =
  let n = U32.v (Char?.code c) in
  if 97 <= n && n <= 122 then Char (U32.uint_to_t (n - 32)) else c

module Typestring

val ca: Type0
val cb: Type0
val cc: Type0
val cd: Type0
val ce: Type0
val cf: Type0
val cg: Type0
val ch: Type0
val ci: Type0
val cj: Type0
val ck: Type0
val cl: Type0
val cm: Type0
val cn: Type0
val co: Type0
val cp: Type0
val cq: Type0
val cr: Type0
val cs: Type0
val ct: Type0
val cu: Type0
val cv: Type0
val cw: Type0
val cx: Type0
val cy: Type0
val cz: Type0
val c0: Type0
val c1: Type0
val c2: Type0
val c3: Type0
val c4: Type0
val c5: Type0
val c6: Type0
val c7: Type0
val c8: Type0
val c9: Type0
val c_: Type0

val string_nil: Type0
val string_cons (c: Type0) (s: Type0): Type0

open FStar.String

let char_t_of_char (c: char): Type0 =
  match c with
  | 'a' -> ca
  | 'b' -> cb
  | 'c' -> cc
  | 'd' -> cd
  | 'e' -> ce
  | 'f' -> cf
  | 'g' -> cg
  | 'h' -> ch
  | 'i' -> ci
  | 'j' -> cj
  | 'k' -> ck
  | 'l' -> cl
  | 'm' -> cm
  | 'n' -> cn
  | 'o' -> co
  | 'p' -> cp
  | 'q' -> cq
  | 'r' -> cr
  | 's' -> cs
  | 't' -> ct
  | 'u' -> cu
  | 'v' -> cv
  | 'w' -> cw
  | 'x' -> cx
  | 'y' -> cy
  | 'z' -> cz
  | '0' -> c0
  | '1' -> c1
  | '2' -> c2
  | '3' -> c3
  | '4' -> c4
  | '5' -> c5
  | '6' -> c6
  | '7' -> c7
  | '8' -> c8
  | '9' -> c9
  | '_' -> c_
  | _ -> c_
  
let rec string_t_of_chars (s: list char): Type0 =
  match s with
  | [] -> string_nil
  | c :: s -> string_cons (char_t_of_char c) (string_t_of_chars s)

let mk_string_t s: Type0 = string_t_of_chars (String.list_of_string s)

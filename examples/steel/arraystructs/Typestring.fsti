module Typestring

val a: Type0
val b: Type0
val c: Type0
val d: Type0
val e: Type0
val f: Type0
val g: Type0
val h: Type0
val i: Type0
val j: Type0
val k: Type0
val l: Type0
val m: Type0
val n: Type0
val o: Type0
val p: Type0
val q: Type0
val r: Type0
val s: Type0
val t: Type0
val u: Type0
val v: Type0
val w: Type0
val x: Type0
val y: Type0
val z: Type0
val zero: Type0
val one: Type0
val two: Type0
val three: Type0
val four: Type0
val five: Type0
val six: Type0
val seven: Type0
val eight: Type0
val nine: Type0
val underscore: Type0

val string_nil: Type0
val string_cons (c: Type0) (s: Type0): Type0

open FStar.String

let char_t_of_char (ch: char): Type0 =
  match ch with
  | 'a' -> a
  | 'b' -> b
  | 'c' -> c
  | 'd' -> d
  | 'e' -> e
  | 'f' -> f
  | 'g' -> g
  | 'h' -> h
  | 'i' -> i
  | 'j' -> j
  | 'k' -> k
  | 'l' -> l
  | 'm' -> m
  | 'n' -> n
  | 'o' -> o
  | 'p' -> p
  | 'q' -> q
  | 'r' -> r
  | 's' -> s
  | 't' -> t
  | 'u' -> u
  | 'v' -> v
  | 'w' -> w
  | 'x' -> x
  | 'y' -> y
  | 'z' -> z
  | '0' -> zero
  | '1' -> one
  | '2' -> two
  | '3' -> three
  | '4' -> four
  | '5' -> five
  | '6' -> six
  | '7' -> seven
  | '8' -> eight
  | '9' -> nine
  | '_' -> underscore
  | _ -> underscore
  
let rec string_t_of_chars (s: list char): Type0 =
  match s with
  | [] -> string_nil
  | c :: s -> string_cons (char_t_of_char c) (string_t_of_chars s)

let mk_string_t s = string_t_of_chars (String.list_of_string s)

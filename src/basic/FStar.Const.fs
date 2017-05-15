#light "off"
module FStar.Const
open FStar.All

open FStar.BaseTypes

type signedness = | Unsigned | Signed
type width = | Int8 | Int16 | Int32 | Int64

(* NB:
    Const_int (_, None) is not a canonical representation for a mathematical integer
    e.g., you can have both
    Const_int("0x3ffffff", None)
    and
    Const_int("67108863", None)
    which represent the same number
    You should do an "FStar.Util.ensure_decimal" on the
    string representation before comparing integer constants.

    eq_const below does that for you
*)

type sconst =
  | Const_effect
  | Const_unit
  | Const_bool        of bool
  | Const_int         of string * option<(signedness * width)> (* When None, means "mathematical integer", i.e. Prims.int. *)
  | Const_char        of char
  | Const_float       of double
  | Const_bytearray   of array<byte> * Range.range
  | Const_string      of array<byte> * Range.range           (* unicode encoded, F#/Caml independent *)
      // JP: does one mean UTF-8 encoded?
  | Const_range       of Range.range                         (* not denotable by the programmer *)
  | Const_reify                                              (* a coercion from a computation to a Tot term *)
  | Const_reflect     of Ident.lid                           (* a coercion from a Tot term to an l-computation type *)

let eq_const c1 c2 =
    match c1, c2 with
    | Const_int (s1, o1), Const_int(s2, o2) ->
      FStar.Util.ensure_decimal s1 = FStar.Util.ensure_decimal s2 &&
      o1=o2
    | Const_bytearray(a, _), Const_bytearray(b, _)
    | Const_string(a, _), Const_string(b, _) -> a=b
    | Const_reflect l1, Const_reflect l2 -> Ident.lid_equals l1 l2
    | _ -> c1=c2

open FStar.Mul
let rec pow2 (x:int) : int =
  match x with
  | 0  -> 1
  | _  -> Prims.op_Multiply 2 (pow2 (x-1))


let bounds signedness width =
    let n =
        match width with
        | Int8 -> 8
        | Int16 -> 16
        | Int32 -> 32
        | Int64 -> 64
    in
    let lower, upper =
      match signedness with
      | Unsigned ->
        0, pow2 n - 1
      | Signed ->
        let upper = pow2 (n - 1) in
        - upper, upper - 1
    in
    lower, upper
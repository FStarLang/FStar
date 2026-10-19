module CherrySmallInt

(* FStarC.SmallInt-c.cherry.fst: signed comparisons, wrapping arithmetic,
   conversions and the array accessors. *)
open FStarC.Effect
module S = FStarC.SmallInt
module IA = FStar.ImmutableArray.Base

let check (b:bool) (n:int) (acc:int) : int = if b then acc else acc * 100 + n

let main () : ML FStar.UInt32.t =
  let m5 = S.of_int (-5) in
  let p7 = S.of_int 7 in
  let e = 0 in
  let e = check (S.show m5 = "-5" && S.show p7 = "7") 1 e in
  let e = check (S.to_int S.(m5 + p7) = 2) 2 e in
  let e = check (S.to_int S.(m5 - p7) = -12) 3 e in
  let e = check S.(m5 < p7 && m5 <= m5 && p7 > m5 && p7 >= p7 && not (p7 < m5)) 4 e in
  let e = check (S.max m5 p7 = p7 && S.min m5 p7 = m5) 5 e in
  let e = check (S.(zero - one) = S.minus_one) 6 e in
  let big = S.of_int 9223372036854775807 in
  let e = check (S.show S.(big + one) = "-9223372036854775808") 7 e in
  let e = check S.(big + one < zero) 8 e in
  let e = check (S.to_int (S.of_char 'a') = 97
                 && S.to_int (S.of_char '\u03b1') = 945) 9 e in
  let arr = IA.of_list ["x"; "y"; "z"] in
  let e = check (S.to_int (S.array_length arr) = 3
                 && S.array_index arr (S.of_int 2) = "z") 10 e in
  let e = check (S.int_compare 3 5 = S.minus_one && S.int_compare 5 5 = S.zero
                 && S.int_compare 6 5 = S.one) 11 e in
  let e = check (S.(string_compare "abc" "abd" < zero)
                 && S.string_compare "q" "q" = S.zero
                 && S.(string_compare "b" "a" > zero)) 12 e in
  if e = 0 then 0ul else 1ul

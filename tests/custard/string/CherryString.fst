module CherryString

(* FStarC.String-c.cherry.fst: [split_on_string] and [split], which search
   for the separator with cherry_str_find64. *)
open FStarC.Effect
module S = FStarC.String

let main () : ML FStar.UInt32.t =
  let ok = S.split_on_string "a,,b," "," = ["a"; ""; "b"; ""] in
  let ok = S.split_on_string "" "," = [] && S.split_on_string "abc" "" = ["abc"] && ok in
  let ok = S.split_on_string "," "," = [""; ""] && S.split_on_string "ab" "abc" = ["ab"] && ok in
  let ok = S.split_on_string "aXYbXYXYc" "XY" = ["a"; "b"; ""; "c"] && ok in
  let ok = S.split_on_string "XXX" "XX" = [""; "X"] && S.split_on_string "aaab" "ab" = ["aa"; ""] && ok in
  let ok = S.split_on_string "\xc3\xa9,\xc3\xbc" "," = ["\xc3\xa9"; "\xc3\xbc"] && ok in
  let ok = S.split ['.'; '/'] "a.b/c..d" = ["a"; "b"; "c"; "d"] && ok in
  if ok then 0ul else 1ul

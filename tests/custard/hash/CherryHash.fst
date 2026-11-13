module CherryHash

(* FStarC.Hash-c.cherry.fst.  [of_string] is [cherry_str_hash], masked to
   63 bits (the vectors are those of its definition in ulib/c/cherry.c);
   [mix], [cmp_hash] and [of_int] on small integers agree with the OCaml
   build. *)
open FStar.All
module H = FStarC.Hash

let check (name:string) (got:string) (want:string) : ML bool =
  if got = want then true
  else (FStar.IO.print_string (name ^ ": got " ^ got ^ ", want " ^ want ^ "\n"); false)

let s (h:H.hash_code) : string = H.string_of_hash_code h

let main () : ML FStar.UInt32.t =
  let ok = true in
  let ok = check "of_string \"\"" (s (H.of_string "")) "2062761817371520746" && ok in
  let ok = check "of_string a" (s (H.of_string "a")) "-1631658829101846308" && ok in
  let ok = check "of_string foobar" (s (H.of_string "foobar")) "-1613525723349264762" && ok in
  let ok = check "of_string utf8" (s (H.of_string "αβγ")) "-385670916043690937" && ok in
  let ok = check "of_string long" (s (H.of_string "FStarC.TypeChecker.Env")) "-3353525574844366251" && ok in
  let ok = check "of_int 42" (s (H.of_int 42)) "42" && ok in
  let ok = check "of_int -1" (s (H.of_int (-1))) "-1" && ok in
  let ok = check "of_int max" (s (H.of_int 4611686018427387903)) "4611686018427387903" && ok in
  let ok = check "of_int min" (s (H.of_int (-4611686018427387904))) "-4611686018427387904" && ok in
  let ok = check "to_int" (string_of_int (H.to_int (H.of_int (-7)))) "-7" && ok in
  (* Values of the OCaml build. *)
  let ok = check "mix" (s (H.mix (H.of_int (-4611686018427387904)) (H.of_int 4611686018427387903)))
                 "-2413445352586521778" && ok in
  let ok = check "mix 17 42" (s (H.mix (H.of_int 17) (H.of_int 42))) "-3676367703804403659" && ok in
  let ok = check "cmp_hash wraps" (string_of_int (H.cmp_hash (H.of_int (-4611686018427387904)) (H.of_int 1)))
                 "4611686018427387903" && ok in
  (* Large integers: deterministic, and the sign and every chunk count. *)
  let big = 1361129467683753853853498429727072845824 in
  let ok = check "big det" (s (H.of_int big)) (s (H.of_int (big + 0))) && ok in
  let ok = (H.cmp_hash (H.of_int big) (H.of_int (-big)) <> 0) && ok in
  let ok = (H.cmp_hash (H.of_int big) (H.of_int (big + 1)) <> 0) && ok in
  let ok = (H.cmp_hash (H.of_int 4611686018427387904) (H.of_int 4611686018427387903) <> 0) && ok in
  if ok then 0ul else 1ul

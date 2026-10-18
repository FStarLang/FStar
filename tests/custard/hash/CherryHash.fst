module CherryHash

(* FStarC.Hash-c.cherry.fst computes the same hash codes as the OCaml build:
   they are observable (SMT symbol names, unit-test output).  The expected
   output was produced by the OCaml realization (FStarC.Hash-ocaml.fst); it
   covers Zarith's small/boxed boundary, multi-limb and negative integers,
   strings of every length mod 4 and non-ASCII ones, and 63-bit wraparound
   in [mix] and [cmp_hash]. *)
open FStar.All
module H = FStarC.Hash

let ints : list int = [0; 1; -1; 42; 4611686018427387903; -4611686018427387904; 4611686018427387904; -4611686018427387905; 9223372036854775807; 18446744073709551615; 18446744073709551616; -18446744073709551616; 1361129467683753853853498429727072845824; -1361129467683753853853498429727072845824; 123456789012345678901234567890123456789]
let strs : list string = [""; "a"; "ab"; "abc"; "abcd"; "abcde"; "hello world"; "Prims.int"; "αβγ"; "FStar.Pervasives.Native.option"]

let p (s:string) : ML unit = FStar.IO.print_string (s ^ "\n")

let rec go_ints (l:list int) : ML unit =
  match l with [] -> () | i :: tl -> p ("of_int " ^ string_of_int i ^ " = " ^ H.string_of_hash_code (H.of_int i)); go_ints tl

let rec go_strs (k:int) (l:list string) : ML unit =
  match l with [] -> () | s :: tl -> p ("of_string #" ^ string_of_int k ^ " = " ^ H.string_of_hash_code (H.of_string s)); go_strs (k+1) tl

let rec fold (acc:H.hash_code) (l:list H.hash_code) : ML H.hash_code =
  match l with [] -> acc | h :: tl -> fold (H.mix acc h) tl

let rec go_mix (acc:H.hash_code) (l:list H.hash_code) : ML unit =
  match l with [] -> () | h :: tl ->
    p ("mix " ^ H.string_of_hash_code h ^ " = " ^ H.string_of_hash_code (H.mix acc h) ^ "; cmp = " ^ string_of_int (H.cmp_hash acc h)); go_mix acc tl

let rec map_ints (l:list int) : ML (list H.hash_code) = match l with [] -> [] | x :: tl -> H.of_int x :: map_ints tl
let rec map_strs (l:list string) : ML (list H.hash_code) = match l with [] -> [] | x :: tl -> H.of_string x :: map_strs tl

let main () : ML FStar.UInt32.t =
  go_ints ints;
  go_strs 0 strs;
  let hs = FStar.List.Tot.append (map_ints ints) (map_strs strs) in
  let acc = fold (H.of_int 17) hs in
  p ("mix fold = " ^ H.string_of_hash_code acc);
  go_mix acc hs;
  p ("mix min max = " ^ H.string_of_hash_code (H.mix (H.of_int (-4611686018427387904)) (H.of_int 4611686018427387903)));
  0ul

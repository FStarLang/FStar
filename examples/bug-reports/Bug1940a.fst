module Bug1940a

(* Original example from Aymeric *)

open FStar.Seq

type alg = | A | B

let length (a:alg) = match a with
  | A -> 32
  | B -> 64

let repr_length (a:alg) = match a with
  | A -> length A
  | B -> length B + 1

let lbytes (n:nat) = lseq nat n

let compressed (a:alg) = lbytes (length a)

let repr (a:alg) = lbytes (repr_length a)

%Fail
let point_decompress (a:alg) (pk:compressed a) : Tot (repr a) = pk

(*
let test (s:compressed B) : Lemma False =
  assert (Seq.length s == 64);
  let s' = point_decompress B s in
  assert (Seq.length s' == 65);
  assert (s == s');
  assert (False)
*)

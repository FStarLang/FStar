module Bug1940b

(* Minimization by Santiago *)

open FStar.Seq

type t = | C 

let f (a:t) =
  match a with
  | C -> 1

let g (a:t) = 
  match a with
  | C -> 2

let u (a:t) = lseq nat (f a)
let v (a:t) = lseq nat (g a)

%Fail
let foo (a:t) (x:u a) : v a = x

(*
let test (s:u C) : Lemma False =
  let s' = foo C s in
  assert (Seq.length s == 1 /\ Seq.length s' == 2)
*)

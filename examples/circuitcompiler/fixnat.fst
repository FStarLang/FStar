(*--build-config
options:--admit_fsi FStar.Set;
other-files:FStar.Set.fsi FStar.Heap.fst FStar.ST.fst FStar.All.fst
--*)
module Fixnat
open IO

val exp2: nat -> Tot nat
let rec exp2 n =
  if n = 0 then 1 else 2*(exp2 (n-1))

type fixnat (n:nat) = x:nat{x < exp2 n}

val log2: #nb:nat{nb > 0} -> (n:fixnat nb) -> Tot (res:nat{res <= nb})
let rec log2 #nb n =
  if n <= 1 then 1
  else 1+(log2 #(nb-1) (n/2))

val ntofn: nat -> n:nat -> fixnat n
let ntofn x n =
  if x < (exp2 n) then x
  else failwith "insufficient precision"

val fn2n: #n:nat -> x:(fixnat n) -> Tot nat
let fn2n #n x = x

(* TODO: what is the semantics of overflow with the add circuit we are using? *)
val add: #n:nat -> n1:(fixnat n) -> n2:(fixnat n) -> Tot (fixnat n)
let rec add #n n1 n2 =
  (n1 + n2) % (exp2 n)

(*let foo () =
  let nsize = 4 in
  let n1 = ntofn 12 nsize in
  let n2 = ntofn 8 nsize in
  let n3 = add #nsize n1 n2 in
  IO.print_string (IO.string_of_int n3)
;;

foo()*)

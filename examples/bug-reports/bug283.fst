(*--build-config
    options:--admit_fsi Set;
    variables:LIB=../../lib;
    other-files:$LIB/bytes.fst 
  --*)

module Xor
open Bytes

(* Encryption *)
assume val blocksize : int
type block = b:bytes{length b = blocksize}  
assume val xor : block -> block -> Tot block


let xor_laws = assume(forall a b. xor a b = xor b a /\ 
                                  xor (xor a b) a = b) 
(* With this separated definition, the lemma test2 can be proved *)
(*
let xor_sym = assume(forall a b. xor a b = xor b a) 
let xor_inv = assume(forall a b. xor (xor a b) a = b)
*)

val test1 : unit -> Lemma (forall a b. xor (xor a b) b = xor (xor b a) b)
let test1 () = ()

val test2' : unit -> Lemma (forall a b. xor (xor a b) b = a) 
let test2' () = test1 ()

val test2 : unit -> Lemma (forall a b. xor (xor a b) b = a) 
let test2 () = ()

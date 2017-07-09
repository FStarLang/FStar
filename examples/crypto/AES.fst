module AES (* concrete implementation of a one-block symmetric cipher *)
open FStar.ST
open FStar.Array

module Bytes = Platform.Bytes

type bytes = Bytes.bytes // TODO unclear why we need this instead of seq byte
type nbytes (n:nat) = b:bytes{Bytes.length b == n}

let blocksize = 32 (* 256 bits *)
let psize = blocksize
let csize = (op_Multiply 2 blocksize)


type plain  = nbytes psize
type cipher = nbytes csize  (* including IV *)


let keysize = 16 (* 128 bits *)
type key = nbytes keysize 

assume val dummy: plain

assume val generated : key -> Tot bool

assume val gen: unit -> key 
assume val dec: key -> cipher -> Tot plain                    (* this function is pure & complete *)  
assume val enc: k:key -> p:plain -> ST (c:cipher { dec k c = p })
  (requires (fun _ -> True)) 
  (ensures (fun h0 _ h -> modifies_none h0 h))

(* this function is not pure (IV); the refinement captures functional correctness *) 

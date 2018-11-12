module Cert.DSA 
open Array

type bytes = seq byte (* concrete byte arrays *) 
type text  = bytes    (* a type abbreviation, for clarity *)

type nbytes (n:nat) = 
  b:bytes{length b == n} (* fixed-length bytes *)

(* we rely on some external crypto library implementing the DSA standard *)

let keysize = 256 
let tagsize = 20  

type vk = nbytes keysize
type sk = nbytes keysize
assume val sk2vk  : sk -> Tot vk
assume val keygen : unit -> sk

type tag = nbytes tagsize

assume val sign   : sk -> text -> tag 
assume val verify : vk -> text -> tag -> Tot bool 



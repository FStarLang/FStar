module Hybrid
open Array
open PKE

(* we idealize first PKE, then SymEnc *)

let pksize = PKE.pksize
let ciphersize = PKE.ciphersize + SymEnc.ciphersize
 
let enc t = 
  let k = SymEnc.keygen true in 
  append 
    (PKE.encrypt pk k) 
    (SymEnc.encrypt k t)

let dec c =
  let c0,c1 = split c PKE.ciphersize in 
  SymEnc.decrypt (PKE.decrypt sk c0) c1 

// let keygen() = PKE.keygen 

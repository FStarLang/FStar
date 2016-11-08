module Flag
open Crypto.Indexing

(* Settings *all* flags to false, for extracting real implementation *) 

//16-10-08 removing any inline here as they seem incompatible with interfaces

let cipher_prf  a = false 
let mac_log       = false
let mac_int1cma a = false 
let prf_cpa       = false  
let safeHS      i = false 
let safeId      i = false 
let mac1_implies_mac_log i = ()
let mac1_implies_prf     i = ()
let safeId_implies_mac1  i = ()
let safeId_implies_cpa   i = ()
let aes_ct        = false

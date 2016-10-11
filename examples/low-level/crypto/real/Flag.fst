module Flag

(* Settings *all* flags to false, for extracting real implementation *) 

//16-10-08 removing any inline here as they seem incompatible with interfaces

let cipher_prf  _ = false 
let mac_log       = false
let mac_int1cma _ = false 
let prf_cpa       = false  
let safeHS      _ = false 
let safeId      _ = false 


let mac1_implies_mac_log _ = ()
let mac1_implies_prf _     = ()
let safeId_implies_mac1 _  = ()
let safeId_implies_cpa __  = ()

module Flag


let aes_prf = false
let chacha20_prf = false

let poly1305_mac1 = false
let ghash_mac1 = false

let mac_log = false

let mac1_implies_mac_log _ =
  ()

let mac1_implies_prf _ =
  ()

let prf_enc _ = false

let prf_enc_implies_mac1 _ =
  ()

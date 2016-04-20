module Test

//let op_Amp_Amp = Prims.op_AmpAmp

let test () = 
  let x = alloc 0 in
  (read x = 1) && (read x = 1)

module RFD
open RFD.A
open RFD.B
let test (v:RFD.B.t) = { v with i=0 }

let test2 = { RFD.A.b = true }

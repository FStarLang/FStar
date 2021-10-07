module RFD
let test (v:RFD.B.t) = { v with i=0 }
let test1 (v:RFD.A.t) = v.b
let test2 = { RFD.A.b = true }
let test3 = { RFDIncluding.b = true }

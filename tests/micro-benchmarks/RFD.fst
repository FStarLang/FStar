module RFD
open RFD.A
open RFD.B
module AA = RFDIncluding
let test (v:RFD.B.t) = { v with i=0 }
let test2 = { RFD.A.b = true }
let test3 = { RFDIncluding.b = true }

module Test1
let x = 0

let x = 1
let y = assert  (1=0)


module Test3
let x = 1
let y = assert (Test2.x - 1 = Test1.x)

#finish

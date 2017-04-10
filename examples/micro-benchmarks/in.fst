module Test1
let x = 0

module Test2
let x = 1
let y = assert  (1=1)


module Test3
let x = 1
let y = assert (Test2.x - 1 = Test1.x)

#finish

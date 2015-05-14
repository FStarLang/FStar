module Test1
let x = 2 + 1 - 1

module Test2
let x = 0
let y = assert  (1=2 - 1)

module Test3
let x = Test1.x  + Test2.x
let y = assert (Test2.x - Test2.x = 0)

module ShortCircuit

let test1 = assert((true || true) = true)
let test2 = assert((true || false) = true)
let test3 = assert((false || true) = true)
let test4 = assert((false || false) = false)

let test1' = assert((true && true) = true)
let test2' = assert((true && false) = false)
let test3' = assert((false && true) = false)
let test4' = assert((false && false) = false)

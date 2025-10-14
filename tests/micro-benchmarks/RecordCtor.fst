module RecordCtor

type a_t = { a: bool }
type ab_t = { a: bool; b: int }
type abc_t = { a: bool; b: int; c: nat }

let a = { a = true }
let ab = { a = false; b = 42 }
let ba = { b = 42; a = false; }
let abc = { a = true; b = 0; c = 100 }


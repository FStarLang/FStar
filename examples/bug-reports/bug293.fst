module Dpairs

val test : (a:int & b:int{a=b}) ->(unit*unit) -> Tot unit
let test (|a, b|) ((),()) =  assert(a = b)

module Bug1427

abstract type stack = list int
  
abstract val is_empty : stack -> Tot bool
let is_empty = Nil? #int

abstract val empty : s:stack{is_empty s}
let empty = []

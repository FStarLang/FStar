module Bug3530

let _ = x:int -> bool
let _ = #x:int -> bool
let _ = #[@@@1]x:int -> bool
let _ = [@@@1]x:int -> bool

let _ = (x:int) -> bool
let _ = (#x:int) -> bool
let _ = (#[@@@1]x:int) -> bool
let _ = ([@@@1]x:int) -> bool

module Bug3292

#set-options "--print_implicits"

let op_Plus #a (x y : a) = (x,y)
let op_Minus #a (x y : a) = (x,y)
let op_Slash #a (x y : a) = (x,y)
let op_Greater #a (x y : a) = (x,y)
let op_Less #a (x y : a) = (x,y)
let op_GreaterEquals #a (x y : a) = (x,y)
let op_LessEquals #a (x y : a) = (x,y)

let _ = 1 + 1
let _ = 1 - 1
let _ = 1 / 1
let _ = 1 > 1
let _ = 1 < 1
let _ = 1 >= 1
let _ = 1 <= 1

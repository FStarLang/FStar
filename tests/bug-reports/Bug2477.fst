module Bug2477

open FStar.Reflection

val my_mktuple2: #a:Type -> #b:Type -> a -> b -> tuple2 a b
let my_mktuple2 #a #b x y = Mktuple2 x y

let test_ok = (`(my_mktuple2 u#0 u#0))
let test_ok2 = (`(Mktuple2 u#0 u#0))

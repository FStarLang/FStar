module Bug2477

open FStar.Reflection.V2

val my_mktuple2: #a:Type -> #b:Type -> a -> b -> tuple2 a b
let my_mktuple2 #a #b x y = Tuple2.Mk x y

let test_ok = (`(my_mktuple2 u#0 u#0))
let test_ok2 = (`(Tuple2.Mk u#0 u#0))

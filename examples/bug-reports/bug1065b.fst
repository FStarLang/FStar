module Bug1065b

assume val f : list (x:int{x>=0}) -> unit

let test (x:list nat) = f x

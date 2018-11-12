module Bug96

noeq type foo0 : (int -> Type) -> int -> Type =
  | MkFoo0 : r:(int -> Type) -> x:int -> r x -> foo0 r x

let test_foo0_1 (r:(int -> Type)) (x:int) (f:foo0 r x) = match f with 
  | MkFoo0 i h -> ()


val test_foo0_2: r:(int -> Type)
        -> x:int
        -> foo0 r x
        -> unit
let test_foo0_2 (r:(int -> Type)) x f = match f with 
  | MkFoo0 i h -> ()


type foo1 (r:(int -> int -> Type)) : int -> int -> Type =
  | MkFoo1 : x:int -> y:int -> r x y -> foo1 r x y

val test_foo1_1: r:(int -> int -> Type)
                 -> x:int
                 -> y:int
                 -> foo1 r x y
                 -> unit
let test_foo1_1 (r:(int -> int -> Type)) _ _ f = match f with
  | MkFoo1 i j h -> ()


type multi (r:(int -> int -> Type)) : int -> int -> Type =
  | Multi_step : x:int -> y:int -> r x y -> multi r x y
                                                  
val test_multi : r:(int -> int -> Type)
          -> (x0:int -> y0:int{r x0 y0} -> unit)
          -> x:int
          -> y:int
          -> multi r x y
          -> unit
let test_multi (r:(int -> int -> Type)) h2 x y h =
  match h with
  | Multi_step x' y' hr -> admit ()

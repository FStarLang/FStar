module Bug96

type multi (r:(int -> int -> Type)) : int -> int -> Type =
  | Multi_step : x:int -> y:int -> r x y -> multi r x y

val foo : r:(int -> int -> Type) ->
      (x0:int -> y0:int{r x0 y0} -> unit) ->
      x:int -> y:int -> multi r x y -> unit
let foo (r:(int -> int -> Type)) h2 x y h =
  match h with
  | Multi_step x' y' hr -> admit()

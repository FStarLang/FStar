module Bug96

type foo : (int -> Type) -> int -> Type =
  | MkFoo : r:(int -> Type) -> x:int -> r x -> foo r x

val bar: r:(int -> Type)
        -> x:int 
        -> foo r x 
        -> unit
let bar (r:(int -> Type)) x f = match f with 
  | MkFoo(* U r x f i h *) i h -> ()

                   
(* type foo (r:(int -> int -> Type)) : int -> int -> Type = *)
(*   | MkFoo : x:int -> y:int -> r x y -> foo r x y *)

(* val bar: r:(int -> int -> Type) *)
(*         -> x:int  *)
(*         -> y:int  *)
(*         -> foo r x y *)
(*         -> unit *)
(* let bar (r:(int -> int -> Type)) _ _ f = match f with  *)
(*   | MkFoo i j h -> () *)

(* type multi (r:(int -> int -> Type)) : int -> int -> Type = *)
(*   | Multi_step : x:int -> y:int -> r x y -> multi r x y *)
                                                  
(* val foo : r:(int -> int -> Type)  *)
(*           (\* -> (x0:int -> y0:int{r x0 y0} -> unit)  *\) *)
(*           -> x:int  *)
(*           -> y:int  *)
(*           -> multi r x y  *)
(*           -> unit *)
(* let foo (r:(int -> int -> Type)) (\* h2 *\) x y h = *)
(*   match h with *)
(*   | Multi_step x' y' hr -> () *)

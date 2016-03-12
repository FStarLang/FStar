module Test

val id : 'a -> Tot 'a 
let id x = x //the type argument is optimized away

let f (x:int) = id x

let g (x:int) = 
  let id' = fun (a:Type) (x:a) -> x in  //also here
  id' int x

let h (x:int) = (fun (a:Type) (x:a) -> x) int x //not here


(* assume val f : int -> GTot bool *)
(* assume val g: x:int -> Ghost unit *)
(*   (True)  *)
(*   (ensures (fun _ -> f x)) *)
  

(* assume type t : int -> Type *)
(* assume val g : int -> Type *)

(* val h : t (f 0) -> Tot bool *)
(* let h (x:t (f 0)) = op_Equality #(t (f 0)) x x *)

(* assume val f : x:int -> GTot int *)


(* assume val g : x:int -> ST int *)
(*   (requires (fun h -> True)) *)
(*   (ensures (fun h0 y h1 ->  *)
(*     f x >= 0 /\ y = 1)) *)
(* //    y = z + 1)) *)



(* assume type t : int -> Type0 *)

(* type state (i:bool) =  *)
(*   | Mk : t (if i then 0 else 1) -> state i *)

(* module Test2 *)
(* open Test *)
(* val f : i:bool -> state i -> Tot (t (if i then 0 else 1)) *)
(* let f i (Mk x) = x *)

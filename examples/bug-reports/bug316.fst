module Bug316
type a (#max:nat) = x:int{ x < max }

(* Works *)
type t (#max:nat) = a #max

(* Works *)
type c (#max:nat) = 
   | C : x:a #max -> c #max

type r (max:nat) = { x:a #max; }